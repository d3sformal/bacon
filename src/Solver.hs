{-# LANGUAGE DataKinds
           , FlexibleInstances
           , FunctionalDependencies
           , GADTs
           , KindSignatures
           , MultiParamTypeClasses
           , RankNTypes
           , ScopedTypeVariables
           , TypeSynonymInstances #-}

module Solver where

import Control.Monad
import Control.Monad.Free
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Data.Singletons
import Expression
import Expression.Z3
import Prelude hiding (log)

import qualified Data.Map as M
import qualified Z3.Monad as Z3

data SolverF (e :: Sort -> *) a where
    Log         :: String -> a -> SolverF e a
    Push        :: a -> SolverF e a
    Pop         :: a -> SolverF e a
    Assert      :: e 'BooleanSort -> a -> SolverF e a
    Check       :: (Bool -> a) -> SolverF e a
    Model       :: SingI s => e s -> (e s -> a) -> SolverF e a
    UnsatCore   :: e 'BooleanSort -> (e 'BooleanSort -> a) -> SolverF e a
    Interpolate :: [e 'BooleanSort] -> ([e 'BooleanSort] -> a) -> SolverF e a
    Eliminate   :: e 'BooleanSort -> (e 'BooleanSort -> a) -> SolverF e a

instance Functor (SolverF e) where
    fmap f (Log s a)          = Log         s  (f a)
    fmap f (Push a)           = Push           (f a)
    fmap f (Pop  a)           = Pop            (f a)
    fmap f (Assert p a)       = Assert      p  (f a)
    fmap f (Check c)          = Check          (f . c)
    fmap f (Model e c)        = Model       e  (f . c)
    fmap f (UnsatCore e c)    = UnsatCore   e  (f . c)
    fmap f (Interpolate es c) = Interpolate es (f . c)
    fmap f (Eliminate e c)    = Eliminate   e  (f . c)

type Solver e = Free (SolverF e)

runSolver :: forall f a. ( IToZ3 f, IFromZ3 f, IShow f ) => Solver (IFix f) a -> IO a
runSolver = Z3.evalZ3 . go where
    go (Pure a)                  = return a
    go (Free (Log s a))          = liftIO (putStrLn s) >> go a
    go (Free (Push a))           = Z3.push  >> go a
    go (Free (Pop  a))           = Z3.pop 1 >> go a
    go (Free (Assert p a))       = toZ3 p >>= Z3.assert >> go a
    go (Free (Check c))          = Z3.check >>= go . c . (== Z3.Sat)
    go (Free (Model e c))        = do
        r <- Z3.getModel
        case r of
            (Z3.Sat, Just m) -> do
                e' <- toZ3 e
                v <- Z3.modelEval m e' True
                case v of
                    Just v' -> go . c =<< fromZ3 v'
                    Nothing -> error $ "failed valuating " ++ show e
            (Z3.Unsat, _) -> error "failed extracting model from unsatisfiable query"
            _             -> error "failed extracting model"
    go (Free (UnsatCore e c)) = do
        app  <- Z3.toApp =<< toZ3 e
        name <- Z3.getSymbolString =<< Z3.getDeclName =<< Z3.getAppDecl app
        as <- case name of
            "and" -> Z3.getAppArgs app
            _     -> mapM toZ3 [e]
        ps <- mapM (const $ Z3.mkFreshBoolVar "p") as
        zipWithM_ (\a p -> Z3.assert =<< Z3.mkIff a p) as ps
        r <- Z3.checkAssumptions ps
        case r of
            Z3.Sat -> error "failed extracting unsat core from satisfiable query"
            Z3.Unsat -> go . c =<< fromZ3 =<< Z3.mkAnd . map (M.fromList (zip ps as) M.!) =<< Z3.getUnsatCore
            Z3.Undef -> error "failed extracting unsat core"
    go (Free (Interpolate []  c)) = go (c [])
    go (Free (Interpolate [_] c)) = go (c [])
    go (Free (Interpolate es  c)) = do
        (e' : es') <- mapM toZ3 es
        q <- foldM (\a g -> Z3.mkAnd . (:[g]) =<< Z3.mkInterpolant a) e' es'
        r <- Z3.local $ Z3.computeInterpolant q =<< Z3.mkParams
        case r of
            Just (Left _) -> error "failed extracting interpolants from satisfiable query"
            Just (Right is) -> go . c =<< mapM fromZ3 is
            Nothing -> error "failed extracting interpolants"
    go (Free (Eliminate e c)) = do
        g <- Z3.mkGoal True True False
        Z3.goalAssert g =<< toZ3 e
        qe  <- Z3.mkTactic "qe"
        aig <- Z3.mkTactic "aig"
        t <- Z3.andThenTactic qe aig
        a <- Z3.applyTactic t g
        go . c =<< fromZ3 =<< Z3.mkAnd =<< Z3.getGoalFormulas =<< Z3.getApplyResultSubgoal a 0

class Monad m => MonadSolver e m | m -> e where
    log         :: String -> m ()
    push        :: m ()
    pop         :: m ()
    assert      :: e 'BooleanSort -> m ()
    check       :: m Bool
    model       :: SingI s => e s -> m (e s)
    unsatcore   :: e 'BooleanSort -> m (e 'BooleanSort)
    interpolate :: [e 'BooleanSort] -> m [e 'BooleanSort]
    eliminate   :: e 'BooleanSort -> m (e 'BooleanSort)

instance MonadSolver e (Solver e) where
    log         s  = liftF $ Log s ()
    push           = liftF $ Push ()
    pop            = liftF $ Pop  ()
    assert      p  = liftF $ Assert p ()
    check          = liftF $ Check id
    model       e  = liftF $ Model e id
    unsatcore   e  = liftF $ UnsatCore e id
    interpolate es = liftF $ Interpolate es id
    eliminate   e  = liftF $ Eliminate e id

instance MonadSolver e (ExceptT a (StateT b (Solver e))) where
    log         s  = lift . lift $ log s
    push           = lift . lift $ push
    pop            = lift . lift $ pop
    assert      p  = lift . lift $ assert p
    check          = lift . lift $ check
    model       e  = lift . lift $ model e
    unsatcore   e  = lift . lift $ unsatcore e
    interpolate es = lift . lift $ interpolate es
    eliminate   e  = lift . lift $ eliminate e

local :: MonadSolver e m => m a -> m a
local ma = push >> ma >>= \r -> pop >> return r
