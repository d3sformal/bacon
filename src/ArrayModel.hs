{-# LANGUAGE DataKinds #-}

module ArrayModel where

import Control.Monad.IO.Class

import Data.Expression
import Data.Expression.Z3

import qualified Z3.Monad as Z3

main :: IO ()
main = Z3.evalZ3 $ do
  Z3.push
  let a = var "a" :: ALia ('ArraySort 'IntegralSort 'IntegralSort)

  -- this assert may either cause Z3 to model a with
  --   1) any array updated with 3 at index 1, or
  --   2) a constant array of 3
  -- the expected behaviour (with no guarantee) is that it chooses 2
  --
  -- in case this assumption is not met, try commenting this assert and hope Z3 picks constant array of 0
  assert (select a (cnst 1) .=. cnst 3)

  z <- toZ3 a
  r <- Z3.getModel
  case r of
    (Z3.Sat, Just m) -> do
      v <- Z3.modelEval m z True
      case v of
        Just v' -> do
          k <- Z3.getAstKind v'
          case k of
            Z3.Z3_APP_AST -> do
              app <- Z3.toApp v'
              name <- Z3.getSymbolString =<< Z3.getDeclName =<< Z3.getAppDecl app
              args <- Z3.getAppArgs app
              case (name, args) of
                ("const", [arg]) -> do
                  s <- Z3.astToString arg
                  liftIO $ print $ "got constant array of " ++ s
                _ -> error "not a constant array"
            _ -> error "unexpected kind of model value"
        Nothing -> error "failed to get value"
    (_, _) -> error "unexpected result of model call"
  Z3.pop 1