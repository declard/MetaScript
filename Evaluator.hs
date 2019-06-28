{-# LANGUAGE OverloadedStrings, TupleSections, RecursiveDo #-}

module MetaScript.Evaluator (
  exec,
  eval,
  apply,
  applyStatic,
  applyFunction,
  primToObject,
  withContext,

  lookupImplicit,
  lookupContext,
  searchVirtual,
  getVirtual,
  searchStatic,
  getStatic,
  readFields,
  getFields,
  setField,

  prototypeName,
  unitName,
  stringName,
  numberName,
  functionName,
  boolName,
  errorName,
  arrayName,
  objectName,
  namedFunctionName,
  createFromName,
  applyName,
  
  prototypePrim,
  unitPrim,
  stringPrim,
  numberPrim,
  functionPrim,
  boolPrim,
  errorPrim,
  arrayPrim,
  objectPrim,
  namedFunctionPrim,
  createFromPrim,
  applyPrim,
  
  emptyFields,
  allocateRoFields,
  allocateFields,
  allocateFieldsMap,
  allocateObject,
  allocateNumber,
  allocateString,
  allocateFunction,
  allocateBool,
  allocateNamedFunction,
  allocateError,
  allocateErrorWith,
  allocateArray,
  
  callCtor
) where

import qualified MetaScript.Parser as P
import MetaScript.Evaluator.Types
import MetaScript.Debugging
import Data.Functor.Identity
import qualified Data.Map.Strict as DM
import qualified Data.List as DL
import Control.Monad.Trans.Maybe
import Control.Monad.State as S
import Data.Text(Text, unpack, pack)
import Control.Applicative
import Data.Either
import Data.Monoid
import Data.Bool
import Data.Maybe
import Control.Monad.Fix
import qualified Data.Traversable as DT
import qualified Data.HashSet as HS
import Data.Int

data Assoc = LAssoc | RAssoc | NAssoc
data OpInfo = OpInfo { oiObject :: Object, oiAssoc :: Assoc, oiPrior :: Integer }
data OpTree = OpApp OpTree Object OpTree | OpExpr P.Expression

lookupImplicit :: Text -> Evaluation Object
lookupImplicit name = do
  obj <- gets $ DM.lookup name . implicit
  maybe (error $ "Looked for " ++ unpack name) return obj

lookupContext name = do
  obj <- gets $ DM.lookup name . explicit
  maybe (lookupImplicit name) readRef obj

searchVirtual :: Object -> Primitive -> Evaluation (Maybe Object)
searchVirtual object idx = search HS.empty [object]
  where search :: HS.HashSet Int64 -> [Object] -> Evaluation (Maybe Object)
        search visited objects = do
          let fieldses = filter (not . (`HS.member` visited) . objectId) $ map getFields objects
          (ids, results, fields) <- unzip3 <$> mapM visit fieldses
          case catMaybes results of
            [v] -> return $ Just v
            [] -> case fields of
                    [] -> return Nothing
                    _ -> search (visited `HS.union` HS.fromList ids) (concat fields)
            results -> do
              arr <- allocateArray results
              idxo <- primToObject idx
              Just <$> allocateErrorWith "Virtual lookup has found more than one variant" [("Target", object), ("Index", idxo), ("Values", arr)]
        visit (Fields _ oid ref) = do
          fields <- readRef ref
          let res = DM.lookup idx fields
          let protos = DM.elems $ DM.filterWithKey filterClause fields
          return (oid, res, protos)
        filterClause (Unique _)_ = True
        filterClause _ _ = False

getVirtual obj idx = do
  field <- searchVirtual obj idx
  let fail = emptyFields >>= \emptyFields -> allocateErrorWith "Virtual lookup failed" [("Target", obj), ("Index", (Primitive emptyFields idx))]
  maybe fail return field

searchStatic obj idx = do
  fields <- readFields obj
  return $ DM.lookup idx fields

getStatic obj idx = searchStatic obj idx >>= maybe (allocateError "Static lookup failed") return

prototypeName = "prototype"
unitName = "Unit"
stringName = "String"
numberName = "Number"
functionName = "Function"
boolName = "Bool"
errorName = "Error"
arrayName = "Array"
objectName = "Object"
namedFunctionName = "NamedFunction"
createFromName = "createFrom"
applyName = "apply"

prototypePrim = Unique prototypeName
unitPrim = Unique unitName
stringPrim = Unique stringName
numberPrim = Unique numberName
functionPrim = Unique functionName
boolPrim = Unique boolName
errorPrim = Unique errorName
arrayPrim = Unique arrayName
objectPrim = Unique objectName
namedFunctionPrim = Unique namedFunctionName
createFromPrim = String createFromName
applyPrim = String applyName

emptyFields = allocateFieldsMap DM.empty

allocateRoFields fields = Fields True <$> newId <*> newRef (DM.fromList fields)
allocateFields fields = allocateFieldsMap (DM.fromList fields)
allocateFieldsMap fields = Fields False <$> newId <*> newRef fields

allocateObject fields = allocateFields fields >>= \fields -> callCtor objectName [Object fields]
allocateNumber number = emptyFields >>= \emptyFields -> callCtor numberName [Primitive emptyFields (Number number)]
allocateString string = emptyFields >>= \emptyFields -> callCtor stringName [Primitive emptyFields (String string)]
allocateFunction context args body = emptyFields >>= \emptyFields -> callCtor functionName [Function emptyFields (ConstructedFunction context args body)]
allocateBool bool = emptyFields >>= \emptyFields -> callCtor boolName [Primitive emptyFields (Bool bool)]
allocateNamedFunction name context args body = do
  name <- allocateString name
  emptyFields <- emptyFields
  callCtor namedFunctionName [name, Function emptyFields (ConstructedFunction context args body)]

allocateError desc = do
  descObj <- allocateString desc
  callCtor errorName [descObj]

allocateErrorWith :: Text -> [(Text, Object)] -> Evaluation Object
allocateErrorWith desc dat = do
  descObj <- allocateString desc
  dataObj <- allocateObject $ map (\(k, v) -> (String k, v)) dat
  callCtor errorName [descObj, dataObj]

allocateArray :: [Object] -> Evaluation Object
allocateArray = callCtor arrayName

callCtor typeName args = do
  typeObj <- lookupImplicit typeName
  typeCtor <- searchVirtual typeObj (String createFromName)
  maybe (error $ "Failed to find ctor for '" <> unpack typeName <> "' type")
        (\(Function _ (ImbeddedFunction func)) -> func args)
        typeCtor

readFields object = case getFields object of
  (Fields _ _ ref) -> readRef ref

withFields object computation = case getFields object of
  (Fields _ _ ref) -> withRef ref computation

getFields (Object fields) = fields
getFields (Function fields _) = fields
getFields (Array fields _) = fields
getFields (Primitive fields _) = fields

setFieldChecked object field value = case getFields object of
  (Fields True _ _) -> error "Unable to set field value on immutable entity"
  _ -> setField object field value

setField object field value = case getFields object of
  (Fields _ _ ref) -> modifyRef ref (DM.insert field value)

primToObject (Number number) = allocateNumber number
primToObject (String string) = allocateString string
primToObject (Bool bool) = allocateBool bool
primToObject (Unique name) = lookupImplicit name

withContext mapping action = do
  oldContext <- get
  put $ mapping oldContext
  result <- action
  put $ oldContext
  return result

byIndex f (Primitive _ idx) = f idx
byIndex _ _ = error "Index must be primitive"

primitive (Primitive _ p) = p
primitive _ = error "Not a primitive"

extractBool :: Object -> Text -> Evaluation Bool
extractBool object source = do
  -- prim <- searchVirtual object boolPrim
  -- return $ case prim of
    -- (Just (Primitive _ (Bool b))) -> b
  return $ case object of
    (Primitive _ (Bool b)) -> b
    _ -> error $ "Failed to extract bool from a clause for '" <> unpack source <> "'"

ifElse c t f = do
  truenessObj <- eval c
  trueness <- extractBool truenessObj "if then else"
  eval $ bool f t trueness

evalFields (k, v) = do
    ko <- eval k
    vo <- eval v
    return (primitive ko, vo)

applyStatic :: Object -> Maybe Object -> [P.Expression] -> Evaluation Object
applyStatic (Function _ func) this exprs = let args = (maybeToList this <>) <$> mapM eval exprs in
  case func of  (ImbeddedMacro func) -> func this exprs
                (ImbeddedFunction func) -> args >>= func
                (ConstructedFunction context fargs body) -> args >>= evaluateFunction body context fargs

applyStatic object this exprs = do
  vargsao <- mapM eval exprs >>= allocateArray
  let errorData = ("Arguments", vargsao) : ("Entity", object) : maybe [] (\this -> ("This", this) : []) this
  allocateErrorWith "Trying to apply non-functional entity" errorData

applyFunction (ImbeddedFunction func) vargs = func vargs
applyFunction (ImbeddedMacro func) vargs = allocateError "Can not apply 'applyFunction' to ImbeddedMacro"
applyFunction (ConstructedFunction context fargs body) vargs = evaluateFunction body context fargs vargs

evaluateFunction body (Context i e) fargs vargs =
  case fargs of
    Fixed args -> do
      if length args /= length vargs
      then do
        argsoa <- mapM allocateString args
        fa <- allocateArray argsoa
        va <- allocateArray vargs
        allocateErrorWith "Wrong parameter count has been given" [("Expected", fa), ("Given", va)]
      else call (zip args vargs)
    Variadic arg -> do
      vargsa <- allocateArray vargs
      call [(arg, vargsa)]
  where call bound = let
          setContext _ = Context (DM.union (DM.fromList bound) i) e
          in withContext setContext (eval body)

apply :: Object -> Maybe Object -> [P.Expression] -> Evaluation Object
-- apply object this exprs = applyStatic object this exprs
apply object this exprs = do
  funcObj <- searchVirtual object applyPrim
  maybe (allocateErrorWith "This entity doesn't support application" [("Entity", object)])
        (\func -> applyStatic func this exprs)
        funcObj
        
mapArgs (P.Variadic ident) = Variadic ident
mapArgs (P.Fixed idents) = if DL.nub idents /= idents then error "Duplicated arguments" else Fixed idents

evalLValue :: (Object -> Object -> Evaluation Object) -> P.LValue -> Evaluation Object

evalLValue f (P.Identifier name) = do
  object <- lookupContext name
  f object object
        
evalLValue f (P.Index lexpr rexpr) = do
  object <- eval lexpr
  idx <- eval rexpr
  byIndex (getStatic object) idx >>= f object
  
evalLValue f (P.DotIndex lexpr rexpr) = do
  object <- eval lexpr
  idx <- eval rexpr
  byIndex (getVirtual object) idx >>= f object

evalLValue f (P.Dot lexpr name) = do
  object <- eval lexpr
  getVirtual object (String name) >>= f object


evalOps lexpr ops = do
  opso <- mapM mkOp ops
  evalNode $ build (OpExpr lexpr, opso)
  where mkOp (op, re) = do
          opo <- lookupContext op
          (assocs, prior) <- getParams opo
          let assoc = case assocs of
                "left" -> LAssoc
                "right" -> RAssoc
                "no" -> NAssoc
                _ -> error "Unexpected associativity type"
          return (OpInfo opo assoc prior, OpExpr re)

        getParams opo = do
          assoco <- searchStatic opo (String "associativity")
          prioro <- searchStatic opo (String "priority")
          case (assoco, prioro) of
            (Just (Primitive _ (String assoc)), Just (Primitive _ (Number prior))) -> return (assoc, prior)
            _ -> return ("left", 0)

        splitBy f xs = s [] xs
          where s _ [] = Left xs
                s l (x : xs) = if f x then Right (reverse l, x, xs) else s (x : l) xs

        splitByMin f (x : xs) = s (f x) [] [x] xs x xs
          where s min left _ right focus [] = (reverse left, focus, right)
                s min left passed right focus (x : xs) = let min' = f x in
                  if min' < min
                    then s min' passed (x : passed) xs x xs
                    else s min left (x : passed) right focus xs

        build (le, []) = le
        build (le, ops) = let
          (l, (co, cre), r) = splitByMin (oiPrior . fst) ops
          build' le l co cre (Left xs) = OpApp (build (le, l)) (oiObject co) (build (cre, xs))
          build' le l co cre (Right (rl, (ro, rre), rr)) = case (oiAssoc co, oiAssoc ro) of
            (NAssoc, _) -> error "no assoc"
            (_, NAssoc) -> error "no assoc"
            (LAssoc, LAssoc) -> let le' = opapp (build (cre, rl)) in build'' le' []
            (RAssoc, RAssoc) -> opapp $ build'' cre rl
            _ -> error "assoc changed"
            where opapp = OpApp (build (le, l)) (oiObject co)
                  build'' e s = build' e s ro rre (sp co rr)
          sp co = splitBy (\v -> oiPrior co == oiPrior (fst v))
          in build' le l co cre (sp co r)

        evalNode (OpExpr e) = eval e
        evalNode (OpApp l (Function _ f) r) = do
          l <- evalNode l
          r <- evalNode r
          applyFunction f [l, r]
        evalNode (OpApp _ o _) = allocateErrorWith "Can't use entity as operator" [("Entity", o)]


-- Program evaluation
eval :: P.Expression -> Evaluation Object

eval (P.Number i) = allocateNumber i

eval (P.String s) = allocateString s

eval (P.Array a) = mapM eval a >>= allocateArray

eval (P.LValue lvalue) = evalLValue (\_ v -> return v) lvalue

eval (P.Operators lexpr ops) = evalOps lexpr ops

eval (P.Block stmts) = withContext id $ last <$> mapM exec stmts

eval (P.Object fields) = do
  elements <- mapM evalFields fields
  result <- allocateObject elements
  objectObj <- lookupImplicit objectName
  setField result objectPrim objectObj
  return result

eval (P.Lambda args expr) = do
  context <- get
  allocateFunction context (mapArgs args) expr

eval (P.Application (P.LValue lvalue@(P.Identifier _)) rexprs) = evalLValue (\this func -> apply func Nothing rexprs) lvalue

eval (P.Application (P.LValue lvalue) rexprs) = evalLValue (\this func -> apply func (Just this) rexprs) lvalue

eval (P.Application lexpr rexprs) = do
  func <- eval lexpr
  apply func Nothing rexprs

eval (P.DotApplication lexpr rexprs) = do
  func <- eval lexpr
  apply func Nothing rexprs

eval (P.If i t) = ifElse i t P.Unit
eval (P.IfElse i t e) = ifElse i t e

eval P.Unit = lookupImplicit unitName


exec :: P.Statement -> Evaluation Object

exec (P.Define var rexpr) = do
  value <- eval rexpr
  ref <- newRef value
  modify (\(Context i e) -> Context i (DM.insert var ref e))
  lookupImplicit unitName

exec (P.While cexpr bexpr) = let
  while = do
    truenessObj <- eval cexpr
    trueness <- extractBool truenessObj "while"
    if trueness then eval bexpr >> while else lookupImplicit unitName
  in while
  
exec (P.For kname vname sexpr bexpr) = do
  when (kname == vname) $ error "Key and value names in 'for' must be different"
  source <- eval sexpr
  fields <- readFields source
  let process (k, v) = do
        kval <- primToObject k
        let adjustContext (Context i e) = Context (DM.insert kname kval (DM.insert vname v i)) e
        withContext adjustContext (eval bexpr)
  mapM_ process $ DM.toList fields
  lookupImplicit unitName
  
exec (P.Function fname args bexpr) = mdo
  (Context imp exp) <- get
  func <- allocateNamedFunction fname newContext (mapArgs args) bexpr
  let newContext = Context (DM.insert fname func imp) exp
  put newContext
  lookupImplicit unitName

exec (P.Set (P.Identifier var) rexpr) = do
  maybeRef <- gets $ DM.lookup var . explicit
  let ref = maybe (error $ unpack $ "Mutable identifier '" <> var <> "' not found, 'set' failed") id maybeRef
  value <- eval rexpr
  writeRef ref value
  lookupImplicit unitName

exec (P.Set (P.Index lexpr iexpr) rexpr) = do
  object <- eval lexpr
  idx <- eval iexpr
  value <- eval rexpr
  byIndex (setFieldChecked object) idx value
  lookupImplicit unitName
  
exec (P.Set (P.DotIndex lexpr iexpr) rexpr) = do
  object <- eval lexpr
  idx <- eval iexpr
  value <- eval rexpr
  byIndex (setFieldChecked object) idx value
  lookupImplicit unitName

exec (P.Set (P.Dot lexpr name) rexpr) = do
  object <- eval lexpr
  value <- eval rexpr
  setFieldChecked object (String name) value
  lookupImplicit unitName
  
exec (P.Execute expr) = eval expr

exec P.Empty = lookupImplicit unitName
