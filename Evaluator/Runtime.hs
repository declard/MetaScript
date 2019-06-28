{-# LANGUAGE OverloadedStrings, RecursiveDo #-}

module MetaScript.Evaluator.Runtime (emptyContext, defBasicTypes, interpret) where

import MetaScript.Debugging

import MetaScript.Evaluator.Types
import MetaScript.Evaluator
import qualified MetaScript.Parser as P
import Data.Functor.Identity
import qualified Data.Map.Strict as DM
import qualified Data.List as DL
import Control.Monad.Trans.Maybe
import Control.Monad.State as S
import Data.IORef
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

createIFunction func = emptyFields >>= \emptyFields -> callCtor functionName [Function emptyFields (ImbeddedFunction func)]
defImpl name object = modify (\(Context i e) -> Context (DM.insert name object i) e) >> return object

argsE name = allocateError $ "The '" <> name <> "' function was called with wrong arguments"

emptyContext = Context DM.empty DM.empty

interpret line = either error (mapM exec) $ P.parseProgram line

macro d f = Function f $ ImbeddedMacro d
function d f = Function f $ ImbeddedFunction d

a <=> b = compare a b
ordComposeM :: Monad m => m Ordering -> m Ordering -> m Ordering
ordComposeM m n = do
    r <- m
    case r of
      EQ -> n
      _ -> return r

defBasicTypes :: Evaluation ()
defBasicTypes = do
  -- minimal runtime
  let name = "name"
      namePrim = String name

  let defPrim name prim = do
        fields <- allocateFields []
        let this = Primitive fields prim
        defImpl name this
        return this
  
  objectObj <- defPrim objectName objectPrim
  unitObj <- defPrim unitName unitPrim
  numberObj <- defPrim numberName numberPrim
  stringObj <- defPrim stringName stringPrim
  boolObj <- defPrim boolName boolPrim
  errorObj <- defPrim errorName errorPrim
  functionObj <- defPrim functionName functionPrim
  namedFunctionObj <- defPrim namedFunctionName namedFunctionPrim
  arrayObj <- defPrim arrayName arrayPrim
  
  let addPrim name typeName typeObj = do
        object <- defPrim name (Unique name)
        setField object typeName typeObj
        return object
  
  trueObj <- defPrim "true" (Bool True)
  falseObj <- defPrim "false" (Bool False)
  
  setField trueObj boolPrim boolObj
  setField falseObj boolPrim boolObj
  
  let objectCreateFrom [o@(Object _)] = do
        oldMap <- readFields o
        -- let newMap = DM.fromList[(objectPrim, objectObj)] `DM.union` oldMap
        let newMap = oldMap
        newFields <- allocateFieldsMap newMap
        return $ Object newFields
      objectCreateFrom _ = argsE "objectCreateFrom"
  
  let numberCreateFrom [(Primitive _ n@(Number _))] = let
            newFields = allocateRoFields [(numberPrim, numberObj)]
        in Primitive <$> newFields <*> pure n
      numberCreateFrom _ = argsE "numberCreateFrom"
  
  let stringCreateFrom [(Primitive _ s@(String _))] = let
            newFields = allocateRoFields [(stringPrim, stringObj)]
        in Primitive <$> newFields <*> pure s
      stringCreateFrom _ = argsE "stringCreateFrom"
  
  let boolCreateFrom [(Primitive _ (Bool b))] = return $ bool falseObj trueObj b
      boolCreateFrom _ = argsE "boolCreateFrom"

  let functionCreateFrom [func] = mdo
        let construct f (Function _ func) = Function f func
            construct _ _ = error "functionCreateFrom.construct"
            thisFunctionObj = construct newFields func
        newFields <- allocateRoFields [(functionPrim, functionObj), (applyPrim, thisFunctionObj)]
        return thisFunctionObj
      functionCreateFrom _ = argsE "functionCreateFrom"
  
  let errorCreateFrom [desc@(Primitive _ (String _))] = allocateObject [(errorPrim, errorObj), (String "description", desc)]
      errorCreateFrom [desc@(Primitive _ (String _)), v] = allocateObject [(errorPrim, errorObj), (String "description", desc), (String "data", v)]
      errorCreateFrom a = allocateArray a >>= \a -> allocateErrorWith "errorCreateFrom" [("data", a)]

  let namedFunctionCreateFrom [n@(Primitive _ (String _)), (Function _ func)] = mdo
        let thisFunctionObj = Function newFields func
        newFields <- allocateRoFields [(functionPrim, namedFunctionObj), (String name, n), (applyPrim, thisFunctionObj)]
        return thisFunctionObj
      namedFunctionCreateFrom _ = argsE "namedFunctionCreateFrom"

  let arrayCreateFrom elements = do
        let newMap = [(prototypePrim, arrayObj)]
        newFields <- allocateFields newMap
        ref <- newRef $ DM.fromList $ zip [0..] elements
        let array = Array newFields ref
        setField array arrayPrim array
        return array
  
  emptyFields >>= \emptyFields -> setField functionObj createFromPrim (function functionCreateFrom emptyFields) -- bootstrap
  
  let adjust (name, ctor, object) = (createIFunction ctor >>= setField object createFromPrim, allocateString name >>= setField object namePrim)
  
  (\(f, s) -> sequence_ f >> sequence_ s) $ unzip $ map adjust
    [
      (objectName, objectCreateFrom, objectObj),
      (numberName, numberCreateFrom, numberObj),
      (stringName, stringCreateFrom, stringObj),
      (boolName, boolCreateFrom, boolObj),
      (functionName, functionCreateFrom, functionObj),
      (errorName, errorCreateFrom, errorObj),
      (namedFunctionName, namedFunctionCreateFrom, namedFunctionObj),
      (arrayName, arrayCreateFrom, arrayObj)
    ]
  
  setField numberObj prototypePrim objectObj
  setField stringObj prototypePrim objectObj
  setField boolObj prototypePrim objectObj
  setField functionObj prototypePrim objectObj
  setField errorObj prototypePrim objectObj
  setField namedFunctionObj prototypePrim functionObj
  setField arrayObj prototypePrim objectObj
  
  prototypeNameObj <- allocateString prototypeName
  prototypeObj <- Primitive <$> (allocateRoFields [(objectPrim, objectObj), (namePrim, prototypeNameObj)]) <*> pure prototypePrim
  defImpl prototypeName prototypeObj
  
  -- additional runtime
  let addMethod name object func = do
        f <- emptyFields
        funcObj <- functionCreateFrom [func f]
        setField object (String name) funcObj
        return funcObj
  
  addMethod "cond" trueObj (macro (let i _ [t, _] = eval t; i _ _ = argsE "true.cond" in i))
  addMethod "cond" falseObj (macro (let i _ [_, f] = eval f; i _ _ = argsE "false.cond" in i))
  
  addMethod "not" trueObj (function (let i [_] = return falseObj; i _ = argsE "true.not" in i))
  addMethod "not" falseObj (function (let i [_] = return trueObj; i _ = argsE "false.not" in i))

  let mkBool = bool falseObj trueObj
  
  let regular v _ _ = v
      inverted _ v _ = v
      neither _ _ v = v
      (errorHandler, nullHandler) = (make "onSuccess" "onFail" "successOrFail", make "onSomething" "onNull" "somethingOrNull")
        where onYes1 o [v] = p o v
              onNo1 (Just o) _ = return o
              onNeither1 (Just o) _ = return o
              onYes2 o [v, _] = p o v
              onNo2 o [_, v] = p o v
              onNeither2 (Just o) [_, _] = return o
              p o v = do
                func <- eval v
                apply func o []
              make :: Text -> Text -> Text -> (IMacro -> IMacro -> IMacro -> IMacro) -> ([(Text, Fields -> Object)])
              make yes no either selector = [
                (yes, macro $ selector onYes1 onNo1 onNeither1),
                (no, macro $ selector onNo1 onYes1 onNeither1),
                (either, macro $ selector onYes2 onNo2 onNeither2)]
  
  nullObj <- addPrim "null" objectPrim objectObj
  
  let addHandler object (name, func) = addMethod name object func
  
  mapM_ (addHandler objectObj) $ errorHandler regular
  mapM_ (addHandler objectObj) $ nullHandler regular
  mapM_ (addHandler errorObj) $ errorHandler inverted
  mapM_ (addHandler errorObj) $ nullHandler neither
  mapM_ (addHandler nullObj) $ errorHandler regular
  mapM_ (addHandler nullObj) $ nullHandler inverted
  
  let mapString f (Primitive _ (String s)) = allocateString $ f s
      mapString _ _ = allocateError "Can't project string"
      mapNumber f (Primitive _ (Number n)) = allocateNumber $ f n
      mapNumber _ _ = allocateError "Can't project number"
      mapBool f (Primitive _ (Bool b)) = allocateBool $ f b
      mapBool _ _ = allocateError "Can't project bool"
  
  addMethod "neg" numberObj (function (let i [n] = mapNumber negate n; i _ = argsE "Number.neg" in i))
  
  addMethod "ownsField" objectObj (function (let i [obj, (Primitive _ idx)] = mkBool . isJust <$> searchStatic obj idx; i _ = argsE "object.ownsField" in i))
  addMethod "hasField" objectObj (function (let i [obj, (Primitive _ idx)] = mkBool . isJust <$> searchVirtual obj idx; i _ = argsE "object.hasField" in i))

  ordObj <- addPrim "Ord" objectPrim objectObj
  ltObj <- addPrim "lt" objectPrim ordObj
  eqObj <- addPrim "eq" objectPrim ordObj
  gtObj <- addPrim "gt" objectPrim ordObj
  addMethod "cond" ltObj (macro (let i _ [l, _, _] = eval l; i _ _ = argsE "lt.cond" in i))
  addMethod "cond" eqObj (macro (let i _ [_, e, _] = eval e; i _ _ = argsE "eq.cond" in i))
  addMethod "cond" gtObj (macro (let i _ [_, _, g] = eval g; i _ _ = argsE "gt.cond" in i))
  
  let mkOrd ord = case ord of LT -> ltObj; EQ -> eqObj; GT -> gtObj
  
  cmpOp <- let  cmpOpImpl [l, r] = let
                  inc = allocateErrorWith "Incomparable entities" [("Left", l), ("Right", r)]
                  in join $ maybe inc (return . mkOrd) <$> evalStateT (runMaybeT (cmpOpFunc l r)) HS.empty
                cmpOpImpl _ = argsE "<=>"
                cmpOpFunc :: Object -> Object -> MaybeT (StateT (HS.HashSet (Int64, Int64)) Evaluation) Ordering
                cmpOpFunc (Primitive _ l) (Primitive _ r) = return $ l <=> r
                cmpOpFunc (Array (Fields _ li _) lr) (Array (Fields _ ri _) rr) = cmpMaps li ri lr rr
                cmpOpFunc (Object (Fields _ li lr)) (Object (Fields _ ri rr)) = cmpMaps li ri lr rr
                cmpOpFunc (Function _ (ConstructedFunction _ la le)) (Function _ (ConstructedFunction _ ra re)) = return $ compare la ra <> compare le re
                cmpOpFunc _ _ = fail ""
                cmpMaps li ri lr rr = do
                  let p = mkPair li ri
                  hs <- lift $ get
                  if HS.member p hs then return EQ else do
                    lm <- readRef lr
                    rm <- readRef rr
                    modify $ HS.insert p
                    cmpOpFuncMaps lm rm
                cmpOpFuncMaps l r =
                  return ((DM.size l) <=> (DM.size r)) `ordComposeM` cmpOpFuncArray (DM.toAscList l) (DM.toAscList r)
                  where cmpOpFuncArray [] [] = return EQ
                        cmpOpFuncArray ((lk, lv):lxs) ((rk, rv):rxs) =
                          return (lk <=> rk) `ordComposeM` cmpOpFunc lv rv `ordComposeM` cmpOpFuncArray lxs rxs
                mkPair li ri = (min li ri, max li ri)
           in emptyFields >>= \emptyFields -> functionCreateFrom [function cmpOpImpl emptyFields]

    
  defOpFunc <- let
      defOpFuncImpl Nothing [P.LValue (P.Identifier name), P.LValue (P.Identifier assoc), P.Number prior, expr] = do
        (Function _ body) <- eval expr
        object <- emptyFields >>= \emptyFields -> functionCreateFrom [function (applyFunction body) emptyFields]
        assoc <- allocateString assoc
        setField object (String "associativity") assoc
        prior <- allocateNumber prior
        setField object (String "priority") prior
        defImpl name object
      defOpFuncImpl _ a = liftIO (display (DumpOptions False 2) a) >> argsE "defOp"
      in emptyFields >>= \emptyFields -> functionCreateFrom [macro defOpFuncImpl emptyFields]
    
  defImpl "defOp" defOpFunc
  
  
  defImpl "compare" cmpOp
  
  interpret "defOp(<=>, left, 4, compare)"
  interpret "function const(v) { (_) => v }"
  interpret "function tryCompare(a, b, l, e, g) { (a <=> b).onSuccess((o) => o.cond(l, e, g)) }"
  interpret "defOp(==, left, 5, (a, b) => tryCompare(a, b, false, true, false))"
  interpret "defOp(!=, left, 5, (a, b) => (a == b).not())"
  interpret "defOp(<, left, 5, (a, b) => tryCompare(a, b, true, false, false))"
  interpret "defOp(<=, left, 5, (a, b) => (a > b).not())"
  interpret "defOp(>, left, 5, (a, b) => tryCompare(a, b, false, false, true))"
  interpret "defOp(>=, left, 5, (a, b) => (a < b).not())"
  interpret "function id(v) { v }"
  
  addMethod "dump" objectObj (function (let
      i [this, Primitive _ (Number n)] = liftIO $ display (DumpOptions False $ fromInteger n) this >> return this
      i _ = argsE "Object.dump"
    in i))
  
  identityObj <- addPrim "Identity" objectPrim objectObj
  interpret $ "Identity.apply = (v) => {'value' : (_) => v, Identity : Identity}"
  
  pairObj <- addPrim "Pair" objectPrim objectObj
  interpret $ "Pair.apply = (f, s) => {" <>
                "'first' : () => f," <>
                "'second' : () => s," <>
                "'apply' : (_, fa, sa) => Pair(f(fa), s(sa))," <>
                "'<*>' : (_, that) => Pair(f(that.first()), s(that.second()))," <>
                "Pair : Pair}"

  addMethod "get" arrayObj (function (let
      i [a@(Array _ ref), i@(Primitive _ (Number n))] = do
        map <- readRef ref
        maybe (allocateErrorWith "Index not found" [("Array", a), ("Index", i)]) return $ DM.lookup n map
      i _ = argsE "Array.get"
    in i))
    
  addMethod "length" arrayObj (function (let
      i [(Array _ ref)] = do
        map <- readRef ref
        allocateNumber $ toInteger $ DM.size map
      i _ = argsE "Array.get"
    in i))
  
  addMethod "set" arrayObj (function (let
      i [a@(Array _ ref), (Primitive _ (Number k)), v] = do
        map <- readRef ref
        writeRef ref $ DM.insert k v map
        return a
      i _ = argsE "Array.set"
    in i))
  
  addMethod "iterate" arrayObj (function (let
      i [(Array _ ref), (Function _ f)] = do
        map <- readRef ref
        mapM_ (\(k, v) -> allocateNumber k >>= \k -> applyFunction f [k, v]) $ DM.toList map
        return unitObj
      i a = allocateArray a >>= \a -> allocateErrorWith "Array.iterate" [("Args", a)]
    in i))
    
  addMethod "indexes" arrayObj (function (let
      i [(Array _ ref)] = do
        map <- readRef ref
        idxs <- mapM allocateNumber $ DM.keys map
        allocateArray idxs
      i _ = argsE "Array.indexes"
    in i))
  
  addMethod "pop" arrayObj (function (let
      i [(Array _ ref)] = do
        map <- readRef ref
        let pop (v, map) = do
              writeRef ref map
              (Function _ func) <- getVirtual identityObj applyPrim
              applyFunction func [v]
        maybe (return nullObj) pop $ DM.maxView map
      i _ = argsE "Array.pop"
    in i))
  
  let generateNumAlg name op = do
          nameObj <- allocateString name
          emptyFields <- emptyFields
          funcObj <- namedFunctionCreateFrom [nameObj, function impl emptyFields]
          defImpl name funcObj
        where impl [Primitive _ (Number l), Primitive _ (Number r)] = op l r
              impl _ = argsE name
  
  generateNumAlg "add" (\l r -> allocateNumber $ l + r)
  generateNumAlg "sub" (\l r -> allocateNumber $ l - r)
  generateNumAlg "mul" (\l r -> allocateNumber $ l * r)
  generateNumAlg "div" (\l r -> if r == 0 then allocateError "Division by zero" else allocateNumber (l `div` r))
  generateNumAlg "mod" (\l r -> if r == 0 then allocateError "Division by zero" else allocateNumber (l `mod` r)) 
  
  interpret "defOp(+, left, 6, add)"
  interpret "defOp(-, left, 6, sub)"
  interpret "defOp(*, left, 7, mul)"
  interpret "defOp(/, left, 7, div)"
  interpret "defOp(\\, left, 7, mod)"
  
  addMethod "argsCount" functionObj (function (let
      i [Function _ f] = countArgs f
      i _ = argsE "Function.argsCount"
      countArgs (ImbeddedFunction _) = return nullObj
      countArgs (ImbeddedMacro _) = return nullObj
      countArgs (ConstructedFunction _ (Variadic _) _) = return nullObj
      countArgs (ConstructedFunction _ (Fixed args) _) = allocateNumber $ DL.genericLength args
    in i))
  
  interpret $ "Array.filter = (this, f) => { var result = []; this.iterate((k, v) => { if (f(v)) result.set(k, v) }); result }"
  interpret $ "Array.map = (this, f) => { var result = []; this.iterate((k, v) => result.set(k, f(v))); result }"
  
  addMethod "applyPoly" functionObj (function (let
      i [Function _ f, Array _ ref] = do
        map <- readRef ref
        applyFunction f $ DM.elems map
      i _ = argsE "Function.applyPoly"
      countArgs (ImbeddedFunction _) = return nullObj
      countArgs (ImbeddedMacro _) = return nullObj
      countArgs (ConstructedFunction _ (Variadic _) _) = return nullObj
      countArgs (ConstructedFunction _ (Fixed args) _) = allocateNumber $ DL.genericLength args
    in i))
  
  interpret $ "Error.apply = Error.createFrom"
  
  addPrim "default" objectPrim objectObj
  
  octotorpFunc <- let f _ [v] = do
                        setContext <- gets const
                        emptyFields <- emptyFields
                        functionCreateFrom [function (\[] -> withContext setContext $ eval v) emptyFields]
                      f _ _ = argsE "#"
                  in emptyFields >>= \emptyFields -> functionCreateFrom [macro f emptyFields]
    
  defImpl "#" octotorpFunc
  
  interpret $ "function case(value, cases) { cases[value].onFail((_) => cases[default].onFail((_) => Error('Non-exhaustive pattern'))).onSuccess((v) => v()) }"
  
  interpret $ "function dispatch funcs {" <>
                "args => {" <>
                  "var count = args.length();" <>
                  "function tryWith(pred) {" <>
                    "var matches = funcs.filter((f) => pred(f.argsCount()));" <>
                    "var ml = matches.length();" <>
                    "ml case {" <>
                      "0 : #(null)," <>
                      "1 : #(Identity(matches.pop().value().applyPoly(args)))," <>
                      "default : #(Error('Ambiguous function list in dispatch'))" <>
                    "}" <>
                  "};" <>
                  "tryWith((f) => f.somethingOrNull((v) => v == count, const(false)))" <>
                  ".onNull(const(tryWith((f) => f.somethingOrNull(const(false), const(true)))))" <>
                "}" <>
              "}"
  
  return ()


-- andOp name = return $ mkIMacro [mkType name] impl
  -- where impl _ [le, re] = do
          -- l <- eval le
          -- case l of (Primitive _ (Bool False)) -> return falseObj
                    -- (Primitive _ (Bool _)) -> eval re
                    -- _ -> allocateError name
        -- impl _ _ = allocateError name

-- orOp name = return $ mkIMacro [mkType name] impl
  -- where impl _ [le, re] = do
          -- l <- eval le
          -- case l of (Primitive _ (Bool True)) -> return trueObj
                    -- (Primitive _ (Bool _)) -> eval re
                    -- _ -> allocateError name
        -- impl _ _ = allocateError name

-- xorOp name = return $ mkIFunc [mkType name] impl
  -- where impl [Primitive _ (Bool l), Primitive _ (Bool r)] = return $ mkBool $ l /= r
        -- impl _ = allocateError name

-- dispatchFunc name = return $ mkIFunc [mkType name] (\funcs -> return $ mkIMacro [] (impl funcs))
  -- where impl funcs _ args = do
          -- matches <- catMaybes <$> mapM m funcs
          -- let sz = length args
              -- best = lookup (Just sz) matches
              -- good = lookup Nothing matches
              -- app f = mapM eval args >>= applyFunc f
          -- fromJust $ (app <$> best) <|> (app <$> good) <|> Just (allocateError "'dispatch': no appropriate functions")
        -- m' (Function _ _ (Fixed a) _) = Just $ length a
        -- m' (Function _ _ _ _) = Nothing
        -- m' (IFunction _ _) = Nothing
        -- m' (IMacro _ _) = Nothing
        -- m'' o = (m' o, o)
        -- m o = do  func <- searchVirtual o (primitive functionObj)
                  -- return $ m'' <$> func


-- cloneWith :: (Map -> Map) -> Object -> Evaluation Object
-- cloneWith func object = case object of
    -- (Object fields) -> Object <$> cloneF fields
    -- (Primitive fields (Unique _)) -> Object <$> cloneF fields
    -- (Function fields c a e) -> cloneF fields >>= \fields -> return $ Function fields c a e
    -- (IFunction fields f) -> cloneF fields >>= \fields -> return $ IFunction fields f
    -- (IMacro fields m) -> cloneF fields >>= \fields -> return $ IMacro fields m
    -- (Array fields aref) -> do
      -- fields <- cloneF fields
      -- a <- readRef aref
      -- aref <- newRef a
      -- return $ Array fields aref
    -- (Primitive fields p) -> cloneF fields >>= \fields -> return $ Primitive fields p
  -- where cloneF (RFields f) = return $ RFields (func f)
        -- cloneF (WFields ref) = do
          -- oldF <- readRef ref
          -- newFRef <- newRef (func oldF)
          -- return $ WFields newFRef
