{-# LANGUAGE OverloadedStrings #-}

module MetaScript.Interpreter (execute, execute', execute'', parseProgram, DumpOptions(..)) where

import MetaScript.Evaluator
import MetaScript.Evaluator.Runtime
import MetaScript.Evaluator.Types
import MetaScript.Debugging
import MetaScript.Parser

import Data.Functor.Identity
import Control.Monad
import Control.Monad.Trans
import qualified Data.Map.Strict as DM
import Data.Text(pack)
import Control.Monad.State

runDefault s = runEvaluation (defBasicTypes >> mapM exec s) emptyContext


{-
stringProto: add, sub
arrayProto: take, sub, insert, +
object: create, clone, createImmutable, +
function: create, +
-}

executeWith d selector = either print (runDefault >=> display d . selector >=> const (putStrLn "")) . parseProgram . pack
execute d = executeWith (DumpOptions { dumpFunctions = True, depth = d }) id
execute' d = executeWith (DumpOptions { dumpFunctions = False, depth = d }) last
execute'' d = executeWith d (const ([] :: [Object]))

--"var f = \\(s) -> \\(n) -> (n == 0).cond(1, n * s(n - 1)); var y = \\(f) -> (\\(x) -> f(\\(y) -> x(x)(y)))(\\(x) -> f(\\(y) -> x(x)(y))); y(f)(4)"

-- execute'' "var y = ((x) => x(x)) ((x) => (w) => w((z) => x(x)(w)(z))); var f = (f) => (x) => (x == 0).cond(1, x * f(x - 1)); closure(y); ()"

--execute'' "var y = ((q) => q(q)) ((x) => (w) => w((z) => x(x)(w)(z))); var id = (e) => (r) => e(r); y(id)(1)"