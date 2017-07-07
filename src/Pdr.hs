{-# LANGUAGE DataKinds
           , FlexibleContexts
           , FlexibleInstances
           , GADTs
           , MultiParamTypeClasses
           , RankNTypes
           , ScopedTypeVariables
           , TypeOperators
           , UndecidableInstances #-}

module Pdr where

import Control.Monad
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Expression
import Prelude hiding (and, or, not, log, init)

import Solver

newtype Cex e = Cex [e 'BooleanSort]
newtype Inv e = Inv (e 'BooleanSort)

instance Show (e 'BooleanSort) => Show (Cex e) where
    show (Cex es) = "cex: " ++ show es

instance Show (e 'BooleanSort) => Show (Inv e) where
    show (Inv s) = "inv: " ++ show s

data Pdr c i e s = Pdr { initial :: ExceptT (c e) (StateT s (Solver e)) ()
                       , search  :: ExceptT (c e) (StateT s (Solver e)) ()
                       , induct  :: ExceptT (i e) (StateT s (Solver e)) () }

pdr :: Pdr c i e s -> StateT s (Solver e) (Either (c e) (i e))
pdr p = either id id <$> runExceptT ( liftL (initial p) >> forever ( liftL (search p) >> liftR (induct p) ) ) where
    liftL = withExceptT Left
    liftR = withExceptT Right
