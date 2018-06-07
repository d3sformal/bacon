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
import Data.Expression
import Data.Expression.Z3 hiding (push, pop, assert, check, model, unsatcore, interpolate, eliminate)
import Data.List
import Data.Singletons
import Data.Typeable
import Prelude hiding (log)

import qualified Data.Map as M
import qualified Prelude as P
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

defaultLog :: Typeable t => t -> Bool
defaultLog = P.not . logExactly Z3Log

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
    go :: Solver (IFix f) b -> StateT SolverContext Z3.Z3 b

    -- Pure values
    go (Pure a) = return a

    -- Logging
    go (Free (Log t m a)) = do
        when (f t) $ do
            i  <- use indentation
            mp <- use lastlog
            case mp of
                Just p  -> when (typeOf t /= p) (liftIO . putStrLn $ "")
                Nothing -> return ()
            lastlog .= Just (typeOf t)
            liftIO . putStrLn . indent' i . show' $ m
        go a

    go (Free (Indent a))   = modify (indentation %~ (+ 1))      >> go a
    go (Free (Unindent a)) = modify (indentation %~ subtract 1) >> go a

    -- Incremental solving
    go (Free (Push a)) = do
        go (log Z3Log "(push)")
        modify $ declarations %~ ([] :)
        lift Z3.push
        go a
    go (Free (Pop  a)) = do
        go (log Z3Log "(pop 1)")
        modify $ declarations %~ (tail)
        lift (Z3.pop 1)
        go a

    -- Assert
    go (Free (Assert p a)) = do
        p' <- lift $ toZ3 p

        when (f Z3Log) $ do
            s <- lift $ Z3.astToString p'
            go . mapM_ (log Z3Log) =<< declare p'
            go . log Z3Log $ "(assert " ++ s ++ ")"

        lift $ Z3.assert p'

        go a

    -- Check
    go (Free (Check c)) = do
        go (log Z3Log "(check-sat)")
        go . c . (== Z3.Sat) =<< lift Z3.check

    -- Model
    go (Free (Model e c)) = do
        e' <- lift $ toZ3 e

        when (f Z3Log) $ do
            s <- lift $ Z3.astToString e'
            go . mapM_ (log Z3Log) =<< declare e'
            go . log Z3Log $ "(get-value (" ++ s ++ "))"

        r <- lift $ do
            r <- Z3.getModel
            case r of
                (Z3.Sat, Just m) -> do
                    v <- Z3.modelEval m e' True
                    case v of
                        Just v' -> fromZ3 v'
                        Nothing -> error $ "failed valuating " ++ show e
                (Z3.Unsat, _) -> error "failed extracting model from unsatisfiable query"
                _             -> error "failed extracting model"

        go (c r)

    -- Unsat core
    go (Free (UnsatCore e c)) = do
        (as, ps) <- lift $ do
            app  <- Z3.toApp =<< toZ3 e
            name <- Z3.getSymbolString =<< Z3.getDeclName =<< Z3.getAppDecl app
            as <- case name of
                "and" -> Z3.getAppArgs app
                _     -> mapM toZ3 [e]
            ps <- mapM (const $ Z3.mkFreshBoolVar "p") as
            return (as, ps)

        when (f Z3Log) $ do
            ass <- lift $ mapM Z3.astToString as
            pss <- lift $ mapM Z3.astToString ps
            go . mapM_ (log Z3Log) . concat =<< mapM declare as
            go . mapM_ (log Z3Log) . concat =<< mapM declare ps
            go . mapM_ (log Z3Log . (\(a, p) -> "(assert (= " ++ p ++ " " ++ a ++ "))")) $ zip ass pss
            go . log Z3Log $ "(check-sat-assuming (" ++ intercalate " " pss ++ "))"
            go . log Z3Log $ "(get-unsat-core)"

        r <- lift $ do
            zipWithM_ (\a p -> Z3.assert =<< Z3.mkIff a p) as ps
            r <- Z3.checkAssumptions ps
            case r of
                Z3.Sat -> error "failed extracting unsat core from satisfiable query"
                Z3.Unsat -> fromZ3 =<< Z3.mkAnd . map (M.fromList (zip ps as) M.!) =<< Z3.getUnsatCore
                Z3.Undef -> error "failed extracting unsat core"

        go (c r)

    -- Interpolation
    go (Free (Interpolate []  c)) = go (log Z3Log "; (compute-interpolant )")  >> go (c [])
    go (Free (Interpolate [_] c)) = go (log Z3Log "; (compute-interpolant _)") >> go (c [])
    go (Free (Interpolate es  c)) = do
        q <- lift $ do
            (e' : es') <- mapM toZ3 es
            foldM (\a g -> Z3.mkAnd . (:[g]) =<< Z3.mkInterpolant a) e' es'

        when (f Z3Log) $ do
            s <- lift $ Z3.astToString q
            go . mapM_ (log Z3Log) =<< declare q
            go . log Z3Log $ "(compute-interpolant " ++ s ++ ")"

        r <- lift $ do
            r <- Z3.local $ Z3.computeInterpolant q =<< Z3.mkParams
            case r of
                Just (Left _)   -> error "failed extracting interpolants from satisfiable query"
                Just (Right is) -> mapM fromZ3 is
                Nothing         -> error "failed extracting interpolants"

        go (c r)

    -- Quantifier elimination
    go (Free (Eliminate e c)) = do
        e' <- lift $ toZ3 e

        when (f Z3Log) $ do
            s <- lift $ Z3.astToString e'
            go . log Z3Log $ "(push)"
            go . mapM_ (log Z3Log) =<< declare e'
            go . log Z3Log $ "(assert " ++ s ++ ")"
            go . log Z3Log $ "(apply (then qe aig))"
            go . log Z3Log $ "(pop 1)"

        r <- lift $ do
            g <- Z3.mkGoal True True False
            Z3.goalAssert g e'
            qe  <- Z3.mkTactic "qe"
            aig <- Z3.mkTactic "aig"
            t <- Z3.andThenTactic qe aig
            a <- Z3.applyTactic t g
            fromZ3 =<< Z3.mkAnd =<< Z3.getGoalFormulas =<< Z3.getApplyResultSubgoal a 0

        go (c r)

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

    declare a = do
        ds  <- lift $ collect a
        dss <- lift $ mapM Z3.funcDeclToString ds
        declare' ds dss
    declare' ds dss = do
        (ds', dss') <- unzip . (\ctx -> filter ((`notElem` ctx) . fst) (zip ds dss)) . concat <$> use declarations
        modify $ declarations . ix 0 %~ (++ ds')
        return dss'

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
