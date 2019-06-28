{-# LANGUAGE OverloadedStrings, TupleSections, FlexibleInstances, OverlappingInstances #-}

module MetaScript.Debugging (display, DumpOptions(..)) where

import MetaScript.Evaluator.Types
import qualified MetaScript.Parser as P

import Control.Concurrent.MVar
import Control.Monad.Identity
import Control.Monad.Trans
import Control.Monad.Trans.Reader
import qualified Data.Text.IO as DTIO
import qualified Data.Map.Strict as DM
import Data.Text(Text, unpack)
import Data.Bool

data DumpOptions = DumpOptions { dumpFunctions :: Bool, depth :: Int }

display d v = runReaderT (dump v) (0, d) >> putStrLn "" >> putStrLn ""

i = do
  l <- asks fst
  p $ concat $ replicate l " "

n = local (\(l, d) -> (l + 1, d))
e (l, d) = (l, d { depth = depth d - 1 })
p = lift . putStr

d v = dump v
dd v = asks snd >>= \opts -> if depth opts > 0 then local e (d v) else p "..."

class Dumpable v where dump :: v -> ReaderT (Int, DumpOptions) IO ()
instance Dumpable Object where
  dump (Object f) = p "(Object " >> dd f >> p ") // Object"
  -- dump (Function f) = p "(Function " >> dd f >> p " _ " >> d a >> p "\n" >> n (i >> d e) >> p "\n" >> i >> p ") // Function"
  dump (Function f func) = p "(Function " >> dd f >> p " " >> d func >> p ") // Function"
  dump (Array f ref) = p "(Array " >> {-dd f >> p " " >> -}dd ref >> p ") // Array"
  dump (Primitive f (Unique name)) = p "(Primitive _ (Unique " >> p (unpack name) >> p ")) // Primitive"
  dump (Primitive f v) = p "(Primitive " >> dd f >> p " " >> d v >> p ") // Primitive"
instance Dumpable Primitive where
  dump (Number num) = p "(Number " >> p (show num) >> p ")"
  dump (String text) = p "(String '" >> p (unpack text) >> p "')"
  dump (Bool bool) = p "(Bool " >> p (show bool) >> p ")"
  dump (Unique name) = p "(Unique " >> p (unpack name) >> p")"
instance Dumpable Fields where
  dump (Fields ro oid ref) = p "(Fields " >> p (show ro) >> p " " >> p (show oid) >> p " " >> dump ref >> p ")"
instance Dumpable Function where
  dump (ImbeddedFunction _) = p "(ImbeddedFunction _)"
  dump (ImbeddedMacro _) = p "(ImbeddedMacro _)"
  dump (ConstructedFunction c a b) = p "(ConstructedFunction _ " >> d a >> (asks (dumpFunctions . snd) >>= bool (return ()) (p " " >> d b)) >> p " _)"
instance Dumpable Arguments where
  dump (Variadic arg) = p "(Variadic " >> p (unpack arg) >> p ")"
  dump (Fixed args) = p "(Fixed " >> p (show args) >> p ")"
instance (Dumpable k, Dumpable v) => Dumpable (DM.Map k v) where
  dump m = d (DM.toList m)
instance Dumpable (DM.Map Object Object) where
  dump m = d (DM.toList m)
-- instance (Dumpable s) => Dumpable (Primitive, s) where
  -- dump (String "apply", _) = p "(String 'apply', _)"
  -- dump (f, s) = p "(,)\n" >> n (i >> d f) >> p "\n" >> n (i >> d s)
instance (Dumpable f, Dumpable s) => Dumpable (f, s) where
  dump (f, s) = p "(,)\n" >> n (i >> d f) >> p "\n" >> n (i >> d s)
instance (Dumpable v) => Dumpable [v] where
  dump [] = p "[]"
  dump list = p "[\n" >> pr list
    where pr [] = p "\n" >> i >> p "]"
          pr (x:xs@(_:_)) = n (i >> d x) >> p "\n" >> pr xs
          pr [x] = n (i >> d x) >> pr []
instance Dumpable Char where
  dump c = lift $ putChar c
instance Dumpable Integer where
  dump n = p $ show n
instance (Dumpable v) => Dumpable (MVar v) where
  dump v = p "(MVar " >> readRef v >>= d >> p ")"
instance Dumpable P.Expression where
  dump e = p "(" >> p (show e) >> p ")"
instance Dumpable Text where
  dump t = p (unpack t)