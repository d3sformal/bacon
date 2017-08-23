{-# LANGUAGE DataKinds
           , FlexibleInstances
           , FunctionalDependencies
           , GADTs
           , KindSignatures
           , MultiParamTypeClasses
           , RankNTypes
           , ScopedTypeVariables
           , TemplateHaskell
           , TypeOperators
           , TypeSynonymInstances #-}

module Solver where

import Control.Lens
import Control.Monad
import Control.Monad.Free
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Data.List
import Data.Singletons
import Data.Typeable
import Expression
import Expression.Z3
import Prelude hiding (log)

import qualified Data.Map as M
import qualified Z3.Monad as Z3

data SolverF (e :: Sort -> *) a where
    Log         :: ( Eq a, Typeable a, Show b, Typeable b ) => a -> b -> c -> SolverF e c
    Indent      :: a -> SolverF e a
    Unindent    :: a -> SolverF e a
    Push        :: a -> SolverF e a
    Pop         :: a -> SolverF e a
    Assert      :: e 'BooleanSort -> a -> SolverF e a
    Check       :: (Bool -> a) -> SolverF e a
    Model       :: SingI s => e s -> (e s -> a) -> SolverF e a
    UnsatCore   :: e 'BooleanSort -> (e 'BooleanSort -> a) -> SolverF e a
    Interpolate :: [e 'BooleanSort] -> ([e 'BooleanSort] -> a) -> SolverF e a
    Eliminate   :: e 'BooleanSort -> (e 'BooleanSort -> a) -> SolverF e a

instance Functor (SolverF e) where
    fmap f (Log t m a)        = Log         t m (f a)
    fmap f (Indent a)         = Indent          (f a)
    fmap f (Unindent a)       = Unindent        (f a)
    fmap f (Push a)           = Push            (f a)
    fmap f (Pop  a)           = Pop             (f a)
    fmap f (Assert p a)       = Assert      p   (f a)
    fmap f (Check c)          = Check           (f . c)
    fmap f (Model e c)        = Model       e   (f . c)
    fmap f (UnsatCore e c)    = UnsatCore   e   (f . c)
    fmap f (Interpolate es c) = Interpolate es  (f . c)
    fmap f (Eliminate e c)    = Eliminate   e   (f . c)

type Solver e = Free (SolverF e)

logAll :: Typeable t => t -> Bool
logAll = const True

logExactly :: ( Eq a, Typeable a, Typeable b ) => a -> b -> Bool
logExactly (a :: a) (b :: b) = case eqT :: Maybe (a :~: b) of
    Just Refl -> a == b
    Nothing   -> False

logZ3 :: Typeable b => b -> Bool
logZ3 = logExactly Z3Log

data Z3Log = Z3Log deriving ( Eq, Typeable )

data SolverContext = SolverContext { _indentation :: Int, _lastlog :: Maybe TypeRep, _declarations :: [[Z3.FuncDecl]] }

makeLenses ''SolverContext

runSolver :: forall f a. ( IToZ3 f, IFromZ3 f, IShow f ) => (forall t. Typeable t => t -> Bool) -> Solver (IFix f) a -> IO a
runSolver f = Z3.evalZ3 . flip evalStateT (SolverContext 0 Nothing []) . go . (log Z3Log "(set-option :produce-unsat-cores true)" >>) where
    go (Pure a)                  = return a
    go (Free (Log t m a))        = do
        when (f t) $ do
            i  <- use indentation
            mp <- use lastlog
            case mp of
                Just p  -> when (typeOf t /= p) (liftIO . putStrLn $ "")
                Nothing -> return ()
            lastlog .= Just (typeOf t)
            liftIO . putStrLn . indent' i . show' $ m
        go a
    go (Free (Indent a))         = modify (indentation %~ (+ 1))      >> go a
    go (Free (Unindent a))       = modify (indentation %~ subtract 1) >> go a
    go (Free (Push a))           = lift  Z3.push   >> modify (declarations %~ ([] :)) >> go (log Z3Log "(push)" >> a)
    go (Free (Pop  a))           = lift (Z3.pop 1) >> modify (declarations %~ tail)   >> go (log Z3Log "(pop 1)"  >> a)
    go (Free (Assert p a))       = go
                                 . (\(s, ds) -> mapM_ (log Z3Log . snd) ds >> log Z3Log ("(assert " ++ s ++ ")") >> a)
                                 <=< (\(s, ds) -> concat <$> use declarations >>= \ds' -> let ds'' = filter ((`notElem` ds') . fst) ds in modify (declarations . ix 0 %~ (++ map fst ds'')) >> return (s, ds''))
                                 <=< lift $ do
        q <- toZ3 p
        Z3.assert q
        s   <- Z3.astToString q
        ds  <- collect q
        dss <- mapM Z3.funcDeclToString ds
        return (s, zip ds dss)
    go (Free (Check c))          = lift Z3.check >>= \a -> go (log Z3Log "(check-sat)" >> c (a == Z3.Sat))
    go (Free (Model e c))        = go
                                 . (\(n, m, ds) -> mapM_ (log Z3Log . snd) ds >> log Z3Log ("(get-value (" ++ n ++ "))") >> c m)
                                 <=< (\(n, m, ds) -> concat <$> use declarations >>= \ds' -> let ds'' = filter ((`notElem` ds') . fst) ds in modify (declarations . ix 0 %~ (++ map fst ds'')) >> return (n, m, ds''))
                                 <=< lift $ do
        r <- Z3.getModel
        case r of
            (Z3.Sat, Just m) -> do
                e' <- toZ3 e
                v <- Z3.modelEval m e' True
                case v of
                    Just v' -> do
                        vn  <- Z3.astToString e'
                        vm  <- fromZ3 v'
                        ds  <- collect e'
                        dss <- mapM Z3.funcDeclToString ds
                        return (vn, vm, zip ds dss)
                    Nothing -> error $ "failed valuating " ++ show e
            (Z3.Unsat, _) -> error "failed extracting model from unsatisfiable query"
            _             -> error "failed extracting model"
    go (Free (UnsatCore e c)) = go . (\a -> log Z3Log "(get-unsat-core)" >> c a) <=< lift $ do
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
            Z3.Unsat -> fromZ3 =<< Z3.mkAnd . map (M.fromList (zip ps as) M.!) =<< Z3.getUnsatCore
            Z3.Undef -> error "failed extracting unsat core"
    go (Free (Interpolate []  c)) = go (log Z3Log "; (compute-interpolant )" >> c [])
    go (Free (Interpolate [_] c)) = go (log Z3Log "; (compute-interpolant _)" >> c [])
    go (Free (Interpolate es  c)) = go
                                  . (\(s, i, ds) -> log Z3Log "(push)" >> mapM_ (log Z3Log . snd) ds >> log Z3Log ("(compute-interpolant " ++ s ++ ")") >> log Z3Log "(pop 1)" >> c i)
                                  <=< (\(s, i, ds) -> concat <$> use declarations >>= \ds' -> let ds'' = filter ((`notElem` ds') . fst) ds in modify (declarations . ix 0 %~ (++ map fst ds'')) >> return (s, i, ds''))
                                  <=< lift $ do
        (e' : es') <- mapM toZ3 es
        q <- foldM (\a g -> Z3.mkAnd . (:[g]) =<< Z3.mkInterpolant a) e' es'
        r <- Z3.local $ Z3.computeInterpolant q =<< Z3.mkParams
        case r of
            Just (Left _) -> error "failed extracting interpolants from satisfiable query"
            Just (Right is) -> do
                qs  <- Z3.astToString q
                qi  <- mapM fromZ3 is
                ds  <- collect q
                dss <- mapM Z3.funcDeclToString ds
                return (qs, qi, zip ds dss)
            Nothing -> error "failed extracting interpolants"
    go (Free (Eliminate e c)) = go
                              . (\(a, s, ds) -> log Z3Log "(push)" >> mapM_ (log Z3Log . snd) ds >> log Z3Log ("(assert " ++ s ++ ")") >> log Z3Log "(apply (then qe aig))" >> log Z3Log "(pop 1)" >> c a)
                              <=< (\(a, s, ds) -> concat <$> use declarations >>= \ds' -> let ds'' = filter ((`notElem` ds') . fst) ds in modify (declarations . ix 0 %~ (++ map fst ds'')) >> return (a, s, ds''))
                              <=< lift $ do
        g <- Z3.mkGoal True True False
        q <- toZ3 e
        Z3.goalAssert g q
        qe  <- Z3.mkTactic "qe"
        aig <- Z3.mkTactic "aig"
        t <- Z3.andThenTactic qe aig
        a <- Z3.applyTactic t g
        r <- fromZ3 =<< Z3.mkAnd =<< Z3.getGoalFormulas =<< Z3.getApplyResultSubgoal a 0
        s <- Z3.astToString q
        ds <- collect q
        dss <- mapM Z3.funcDeclToString ds
        return (r, s, zip ds dss)

    collect = fmap M.keys . flip execStateT M.empty . collect'
    collect' a = do
        k <- lift (Z3.getAstKind a)
        case k of
            Z3.Z3_VAR_AST -> return ()
            Z3.Z3_NUMERAL_AST -> return ()
            Z3.Z3_APP_AST -> do
                app <- lift (Z3.toApp a)
                d   <- lift (Z3.getAppDecl app)
                n   <- lift (Z3.getSymbolString =<< Z3.getDeclName d)
                mapM_ collect' =<< lift (Z3.getAppArgs app)
                modify (if builtin n then id else M.insert d True)
            Z3.Z3_QUANTIFIER_AST -> collect' =<< lift (Z3.getQuantifierBody a)
            _ -> error "unknown kind of expression being logged"

    builtin = (`elem` ["=", "<", "<=", ">=", "not", "and", "or", "iff", "true", "false", "+", "-", "*", "select", "store", "interp"])

    show' (m :: m) = case eqT :: Maybe (m :~: String) of
        Just Refl -> m
        Nothing   -> show m

    indent' i = merge . map indent'' . split where
        split = split' [] where
            split' acc [] = [reverse acc]
            split' acc ('\n' : cs) = reverse acc : split' [] cs
            split' acc (c    : cs) = split' (c : acc) cs
        merge = intercalate "\n"

        indent'' "" = ""
        indent'' s'  = (iterate (('\t' :) .) id !! i) s'

class Monad m => MonadSolver e m | m -> e where
    log         :: ( Eq a, Typeable a, Show b, Typeable b ) => a -> b -> m ()
    indent      :: m ()
    unindent    :: m ()
    push        :: m ()
    pop         :: m ()
    assert      :: e 'BooleanSort -> m ()
    check       :: m Bool
    model       :: SingI s => e s -> m (e s)
    unsatcore   :: e 'BooleanSort -> m (e 'BooleanSort)
    interpolate :: [e 'BooleanSort] -> m [e 'BooleanSort]
    eliminate   :: e 'BooleanSort -> m (e 'BooleanSort)

instance MonadSolver e (Solver e) where
    log         t m = liftF $ Log t m ()
    indent          = liftF $ Indent ()
    unindent        = liftF $ Unindent ()
    push            = liftF $ Push ()
    pop             = liftF $ Pop  ()
    assert      p   = liftF $ Assert p ()
    check           = liftF $ Check id
    model       e   = liftF $ Model e id
    unsatcore   e   = liftF $ UnsatCore e id
    interpolate es  = liftF $ Interpolate es id
    eliminate   e   = liftF $ Eliminate e id

instance MonadSolver e (ExceptT a (StateT b (Solver e))) where
    log         t m = lift . lift $ log t m
    indent          = lift . lift $ indent
    unindent        = lift . lift $ unindent
    push            = lift . lift $ push
    pop             = lift . lift $ pop
    assert      p   = lift . lift $ assert p
    check           = lift . lift $ check
    model       e   = lift . lift $ model e
    unsatcore   e   = lift . lift $ unsatcore e
    interpolate es  = lift . lift $ interpolate es
    eliminate   e   = lift . lift $ eliminate e

nest :: MonadSolver e m => m a -> m a
nest ma = indent >> ma >>= \r -> unindent >> return r

local :: MonadSolver e m => m a -> m a
local ma = push >> ma >>= \r -> pop >> return r
