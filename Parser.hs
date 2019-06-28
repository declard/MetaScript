{-# LANGUAGE OverloadedStrings #-}
-- TODO fix @if then else, add for, function, @//, @/* */
module MetaScript.Parser (Statement(..), Expression(..), Arguments(..), LValue(..), parseProgram) where

import Control.Applicative
import Control.Monad
import Data.Attoparsec.Text as AP
import Data.Attoparsec.Combinator as AC
import Data.Either
import qualified Data.Map.Strict as DM
import Data.Monoid
import Data.Text as DT
import Data.Text.IO as DTIO
import Data.List

data LValue = Index Expression Expression | DotIndex Expression Expression | Dot Expression Name | Identifier Name deriving(Show, Eq, Ord)
data Statement =  Define Name Expression
                | While Expression Expression
                | For Text Text Expression Expression
                | Function Text Arguments Expression
                | Set LValue Expression
                | Execute Expression
                | Empty deriving(Show, Eq, Ord)
data Expression = Number Integer
                | String Text
                | Array [Expression]
                | Object [(Expression, Expression)]
                | Lambda Arguments Expression
                | Application Expression [Expression]
                | DotApplication Expression [Expression]
                | Operators Expression [(Name, Expression)]
                | Block [Statement]
                | If Expression Expression
                | IfElse Expression Expression Expression
                | LValue LValue
                | Unit deriving(Show, Eq, Ord)

data Arguments = Fixed [Name] | Variadic Name deriving(Show, Eq, Ord)
type Name = Text

parseProgram = parseOnly program

spaces = many' space
spaces1 = many1' space
surround l r p = l *> p <* r
surround1 s = surround s s
spaced = surround1 spaces
surroundByString l r = surround (string l) (string r)
surroundByStr1 s = surround1 (string s)
paren = surroundByString "(" ")"
bracket = surroundByString "[" "]"
brace = surroundByString "{" "}"
list p = sepBy p (string ",")
parenList = paren . list

numeric = Number <$> decimal
stringy = String <$> surroundByStr1 "'" (AP.takeWhile (notInClass "'"))

reserved = ["if", "else", "while", "for", "function", "var", "=>", ":", "=", "."]

nameIdentifier = do
  x <- satisfy (inClass "_a-zA-Z")
  xs <- AP.takeWhile (inClass "_a-zA-Z0-9")
  return $ cons x xs
  
opChars = "-:!#$%&*+/\\<=>?@\\^|~"
opIdentifier = longIdentifier <|> shortIdentifier
longIdentifier = do
  x <- satisfy (inClass opChars)
  xs <- AP.takeWhile1 (inClass opChars)
  return $ cons x xs
  
shortIdentifier = do
  x <- satisfy (inClass (opChars \\ "=:\\"))
  xs <- AP.takeWhile (inClass opChars)
  return $ cons x xs

name p = do
  id <- spaced p
  if id `elem` reserved then fail "Reserved" else return id

alphaName = name nameIdentifier
opName = name opIdentifier
anyName = alphaName <|> opName

identifier = Identifier <$> anyName
variable = LValue <$> identifier

array = Array <$> bracket (list expression)
object = Object <$> brace (list field)
field = do
  key <- expression
  void $ string ":"
  value <- expression
  return (key, value)

lambda = do
  a <- args
  void $ spaced (string "=>")
  b <- expression
  return $ Lambda a b
  
args = (Variadic <$> anyName) <|> (Fixed <$> parenList anyName)
block = brace $ Block <$> statements  

ifthenelse = do
  void $ string "if"
  i <- spaced $ paren expression
  t <- expression
  e <- option Nothing $ do
    void $ string "else"
    Just <$> expression
  return $ maybe (If i t) (IfElse i t) e

while = do
  void $ string "while"
  c <- spaced $ paren expression
  b <- expression
  return $ While c b

for = do
  void $ string "for"
  (k, v, s) <- spaced $ paren forClause
  b <- expression
  return $ For k v s b
  where forClause = do
          k <- anyName
          void $ string ","
          v <- anyName
          void $ string ":"
          s <- expression
          return (k, v, s)

function = do
  void $ string "function"
  void $ spaces1
  n <- anyName
  a <- args
  b <- spaced block
  return $ Function n a b

unit = string "()" >> pure Unit
term = choice [unit, ifthenelse, numeric, stringy, variable, array, object, paren expression, block]

spanning = do
  head <- term
  accessors <- many $ spaced accessors'
  return $ growTree head accessors
  where growTree root [] = root
        growTree root (x : xs) = growTree (x root) xs
        accessors' = (index' <$> bracket expression)
                      <|> (application' <$> parenList expression)
                      <|> (string "." *> (
                            (dotIndex' <$> bracket expression)
                        <|> (dotApplication' <$> parenList expression)
                        <|> (dot' <$> anyName)))
        index' x root = LValue (Index root x)
        application' x root = Application root x
        dotApplication' x root = DotApplication root x
        dotIndex' x root = LValue (DotIndex root x)
        dot' x root = LValue (Dot root x)

operation = do
  head <- spanning
  operators <- many ((,) <$> anyName <*> spanning)
  return $ case operators of
    [] -> head
    _ -> Operators head operators

expression = spaced $ lambda <|> operation

definition :: Parser Statement
definition = do
  void $ spaces
  void $ string "var"
  i <- anyName
  void $ string "="
  e <- expression
  return $ Define i e

set :: Parser Statement
set = Set <$> (accessor <|> identifier) <* (AP.takeWhile (inClass opChars) >>= \l -> if l == "=" then return () else fail "expected '='") <*> expression
exec :: Parser Statement
exec = Execute <$> expression

accessor = do
  head <- spaced term
  accessors <- many1 accessors'
  return $ growTree head accessors
  where growTree (LValue root) [] = root
        growTree root (x : xs) = growTree (x root) xs
        accessors' = (spaced $ index' <$> bracket expression)
                      <|> (string "." *> ((dotIndex' <$> bracket expression)
                      <|> (dot' <$> anyName)))
        index' x root = LValue (Index root x)
        dotIndex' x root = LValue (DotIndex root x)
        dot' x root = LValue (Dot root x)

emptyStmt = Empty <$ spaces

statement = choice [definition, while, for, function, set, exec, emptyStmt]
statementDelim = spaced (satisfy (inClass ";\n\r"))
statements = surround1 (many' statementDelim) $ statement `sepBy` (many1' statementDelim)

program = statements <* endOfInput