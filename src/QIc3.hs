{-# LANGUAGE DataKinds
           , FlexibleContexts
           , FlexibleInstances
           , FunctionalDependencies
           , GADTs
           , GeneralizedNewtypeDeriving
           , KindSignatures
           , MultiParamTypeClasses
           , RankNTypes
           , ScopedTypeVariables
           , TemplateHaskell
           , TypeApplications
           , TypeOperators
           , UndecidableInstances #-}

module QIc3 where

import Algebra.Lattice
import Control.Arrow
import Control.Comonad.Trans.Coiter
import Control.Lens hiding ((%~), pre, imapM, Const)
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Control.Zipper
import Data.Expression
import Data.List hiding (and, or, init)
import Data.Maybe
import Data.Singletons
import Data.Singletons.Decide
import Data.Typeable
import Prelude hiding (and, or, not, log, init)

import Pdr
import Solver

import qualified Data.Functor.Const as F
import qualified Prelude as P

data Ic3State e = Ic3State { _frames     :: Top :>> [e 'BooleanSort] :>> e 'BooleanSort
                           , _predicates :: [e 'BooleanSort] }

makeLenses ''Ic3State

type Ic3 r e a = ExceptT (r e) (StateT (Ic3State e) (Solver e)) a

getPreviousFrame, getCurrentFrame, getNextFrame :: Ic3 a e (e 'BooleanSort)
getPreviousFrame = lift $ view focus . tug rightward <$> use frames
getCurrentFrame  = lift $ view focus                 <$> use frames
getNextFrame     = lift $ view focus . tug leftward  <$> use frames

goToFirstFrame, goToLastFrame :: Ic3 a e ()
goToFirstFrame = lift $ frames %= rightmost
goToLastFrame  = lift $ frames %= leftmost

goFrameForth, goFrameBack :: Ic3 a e ()
goFrameForth = lift $ frames %= tug leftward
goFrameBack  = lift $ frames %= tug rightward

isFirstFrame, isLastFrame :: Ic3 a e Bool
isLastFrame  = lift $ isNothing . leftward <$> use frames
isFirstFrame = lift $ isNothing . rightward <$> use frames

pushFrame :: e 'BooleanSort -> Ic3 a e ()
pushFrame f = lift $ frames %= \fs -> zipper (f : rezip fs) & fromWithin traverse

modifyFrame :: (e 'BooleanSort -> e 'BooleanSort) -> Ic3 a e ()
modifyFrame f = lift $ frames . focus %= f

getCurrentFrameNum :: Ic3 a e Int
getCurrentFrameNum = lift $ subtract 1 . uncurry (-) . (teeth &&& tooth) <$> use frames

getPredicates :: ( IFoldable f, MaybeQuantified f, e ~ IFix f ) => Ic3 a e ([e 'BooleanSort], [e 'BooleanSort])
getPredicates = lift $ partition isQuantifierFree <$> use predicates

getQuantifierFreePredicates :: ( IFoldable f, MaybeQuantified f, e ~ IFix f ) => Ic3 a e [e 'BooleanSort]
getQuantifierFreePredicates = fst <$> getPredicates

getQuantifiedPredicates :: ( IFoldable f, MaybeQuantified f, e ~ IFix f ) => Ic3 a e [e 'BooleanSort]
getQuantifiedPredicates = snd <$> getPredicates

-- may not work for quantified formulas (predicates to be added) due to "complement" (we will check this)
addPredicates :: ComplementedLattice (e 'BooleanSort) => Eq (e 'BooleanSort) => [e 'BooleanSort] -> Ic3 a e ()
addPredicates ps = lift $ predicates %= nubBy (\a b -> a == b || a == complement b) . (++ ps)

data Ic3Log = Ic3Log deriving ( Eq, Typeable )

logIc3 :: Typeable b => b -> Bool
logIc3 = logExactly Ic3Log

ic3 :: forall e f. ( ComplementedLattice (e 'BooleanSort)
                   , MonadSolver e (Solver e)
                   , Show (e 'BooleanSort)
                   , Eq (e 'BooleanSort)
                   , e ~ IFix f
                   , VarF :<: f
                   , VarF :<<: f
                   , ArithmeticF :<: f
                   , ArrayF :<: f
                   , EqualityF :<: f
                   , ConjunctionF :<: f
                   , DisjunctionF :<: f
                   , MaybeQuantified f
                   , IEq1 f
                   , IShow f
                   , IFoldable f
                   , ITraversable f )
    => [DynamicallySorted e]
    -> e 'BooleanSort
    -> e 'BooleanSort
    -> e 'BooleanSort
    -> Solver e (Either (Cex e) (Inv e))
ic3 vs i t p = flip evalStateT (Ic3State (zipper [i] & fromWithin traverse) (literals i ++ literals p)) . pdr $ Pdr init bad fix where
    init :: Ic3 Cex e ()
    init = do
        -- check init /\ not prop
        log Ic3Log $ "i: " ++ show i
        log Ic3Log $ "t: " ++ show t
        log Ic3Log $ "p: " ++ show p
        local $ do
            log Ic3Log "init: enumerating the initial state with negated property"
            bs <- enumerate (i /\ complement p)
            log Ic3Log $ "init: bad states = " ++ show bs
            unless (null bs) $ throwE (Cex [head bs])

    bad :: Ic3 Cex e ()
    bad = do
        -- check post(top frame) /\ not prop
        n  <- getCurrentFrameNum
        c  <- getCurrentFrame
        log Ic3Log $ "iter" ++ show n ++ ":"
        log Ic3Log $ "bad: cur frame " ++ show n ++ " = " ++ show c
        bad'

    bad' :: Ic3 Cex e ()
    bad' = do
        c  <- getCurrentFrame
        n  <- getCurrentFrameNum
        log Ic3Log "bad': enumerating post-frame with negated property"
        bs <- enumerate (post c /\ complement p)
        log Ic3Log $ "bad': bad states = " ++ show bs
        unless (null bs) $ do
            log Ic3Log $ "\tpost(f" ++ show n ++ "): " ++ show (post c) ++ "\n"
            catchE (mapM_ (block []) bs) $ \(Cex trace) -> do
                let trace' = zipWith ($) (iterate (prime .) id) (map (/\ t) (P.init trace) ++ [last trace])
                log Ic3Log "\tabstract counterexample: "
                mapM_ (log Ic3Log . ("\t\t" ++) . show) trace'
                log Ic3Log ""
                r <- nonEmpty (meets trace')
                if r then throwE . Cex =<< concretiseTrace trace'
                else do
                    log Ic3Log $ "trace: " ++ show trace'
                    trace'' <- generaliseTrace trace'
                    log Ic3Log $ "generalised trace: " ++ show trace''
                    is <- concatMap (literals . unprime) <$> interpolate trace''
                    log Ic3Log "\trefinement (added predicates): "
                    mapM_ (log Ic3Log . ("\t\t" ++) . show) is
                    addPredicates is
                    qfps <- getQuantifierFreePredicates
                    log Ic3Log $ "\tquantifier-free predicates: " ++ show (length qfps)
                    mapM_ (log Ic3Log . ("\t\t" ++) . show) qfps
                    qps <- getQuantifiedPredicates
                    log Ic3Log $ "\tquantified predicates: " ++ show (length qps)
                    mapM_ (log Ic3Log . ("\t\t" ++) . show) qps
                    log Ic3Log ""
                    goToLastFrame
            bad'

    empty :: e 'BooleanSort -> Ic3 a e Bool
    empty s = P.not <$> nonEmpty s

    nonEmpty :: e 'BooleanSort -> Ic3 a e Bool
    nonEmpty s = local $ do
        log Ic3Log "\tchecking non-empty:"
        assert s
        r <- check
        showCheckResult s r
        return r

    enumerate :: e 'BooleanSort -> Ic3 a e [e 'BooleanSort]
    enumerate s = do
        let qf = filter isQuantifierFree (conjuncts s)

        qfcs <- local $ assert (meets qf) >> enumerate'
        qps  <- getQuantifiedPredicates

        flip filterM [ a /\ meets b | a <- qfcs, b <- sequence (map (\c -> [c, complement c]) qps) ] $ \f -> local $ do
            assert s
            assert f
            check

    enumerate' :: Ic3 a e [e 'BooleanSort]
    enumerate' = do
        r <- check
        if r then do
            c  <- cube
            cs <- local $ do
                assert (complement c)
                enumerate'
            return (c : cs)
        else return []

    prime :: forall s. e s -> e s
    prime = (`substitute` Substitution (\v -> case match v of { Just (Var n s) -> Just . inject $ Var (n ++ "'") s; _ -> Nothing }))

    prime' :: forall s. Int -> e s -> e s
    prime' n = foldr (.) id (replicate n prime)

    unprime :: forall s. e s -> e s
    unprime = (`substitute` Substitution (\v -> case match v of { Just (Var n s) -> Just . inject $ Var (filter (/= '\'') n) s; _ -> Nothing }))

    flipPrime :: forall s. e s -> e s
    flipPrime = (`substitute` Substitution (\v -> case match v of { Just (Var n s) -> Just . inject $ Var (if last n == '\'' then filter (/= '\'') n else n ++ "'") s; _ -> Nothing }))

    concretiseTrace :: [e 'BooleanSort] -> Ic3 a e [e 'BooleanSort]
    concretiseTrace tr = local $ do
        assert (meets tr)

        let arridxs = extractArrayIndexExpressions tr

        forM [0 .. length tr - 1] $ \s -> do
            let bs = mapMaybe toStaticallySorted vs :: [e 'BooleanSort]
                is = mapMaybe toStaticallySorted vs :: [e 'IntegralSort]
                ais = nub $ map (\(arr, idx) -> (unprime arr, unprime idx)) arridxs

            a <- fmap meets . forM bs $ \v -> model (prime' s v) >>= \b -> if b == top then return v else return (complement v)
            b <- fmap meets . forM is $ \v -> (v .=.) <$> model (prime' s v)
            c <- fmap meets . forM ais $ \(arr, idx) -> (select arr idx .=.) <$> model (prime' s (select arr idx))

            return (a /\ b /\ c)

    generaliseTrace :: [e 'BooleanSort] -> Ic3 a e [e 'BooleanSort]
    generaliseTrace [] = error "the impossible happend"
    generaliseTrace (i : t) = do
        let i' = abstractConstants i
            t' = i' : t

        r <- nonEmpty $ meets t'

        return $ if r then t else t'

    abstractConstants :: forall (s :: Sort). e s -> e s
    abstractConstants e =
        let freshVars = map (var :: VariableName -> e 'IntegralSort) . toList $ freenames e
            constants = cnsts e in

            -- consider avoiding abstraction of pc = 0

            substitute e (freshVars `forN` constants) where

                toList :: Coiter a -> [a]
                toList c = let (h, t) = runCoiter c in h : toList t

                forN :: forall (s :: Sort). [e s] -> [e s] -> Substitution f
                forN as bs = mconcat $ zipWith for as bs

    cube :: Ic3 a e (e 'BooleanSort)
    cube = do
        ps <- getQuantifierFreePredicates
        bs <- mapM model ps
        return . meets $ (zipWith literal ps bs :: [e 'BooleanSort])

    literal :: e 'BooleanSort -> e 'BooleanSort -> e 'BooleanSort
    literal a v | v == top    = a
                | v == bottom = complement a
                | otherwise  = error $ "failed to determine phase of " ++ show a

    block :: [e 'BooleanSort] -> e 'BooleanSort -> Ic3 Cex e ()
    block trace b = do
        let trace' = b : trace

        c   <- getCurrentFrame
        n   <- getCurrentFrameNum

        bot <- isFirstFrame

        -- if we omit the constraint (/\ complement b) we are trying to prove a stronger property (more then inductivity)
        -- but we can't simply add the constraint without needing to add AbsRelInd from Griggio et al. TACAS14
        pbs <- enumerate (c {- /\ complement b -} /\ pre b)

        log Ic3Log $ "block: prev bad states = " ++ show pbs

        unless (null pbs) $
            if bot
            then throwE (Cex $ head pbs : trace')
            else forM_ pbs $ \b' -> do
                log Ic3Log $ "\t" ++ show n ++ ": pre(b): " ++ show b' ++ "\n"
                c' <- getCurrentFrame
                e  <- empty (c' /\ b')
                unless e $ do
                    goFrameBack
                    block trace' b'
                    goFrameForth
                    c'' <- getPreviousFrame
                    s   <- generalise c'' b'
                    log Ic3Log $ "\tf0" ++ (if n == 0 then "" else if n == 1 then ", f1" else if n == 2 then ", f1, f2" else  ", ..., f" ++ show n) ++ " \\ " ++ show s
                    blockHenceBack s

    blockHenceBack :: e 'BooleanSort -> Ic3 a e ()
    blockHenceBack s = do
        f <- getCurrentFrame
        n <- getCurrentFrameNum
        r <- local $ assert (f /\ s) >> check
        when r $ do
            log Ic3Log $ "blocking in frame " ++ show n ++ " : " ++ show s
            modifyFrame (/\ complement s)
        bot <- isFirstFrame
        unless bot $ do
            goFrameBack
            blockHenceBack s
            goFrameForth

    fix = do
        pushFrame p
        goToFirstFrame
        fix' bottom top

    fix' prev ind = do
        modifyFrame (/\ ind)

        c <- getCurrentFrame
        k <- getCurrentFrameNum

        log Ic3Log $ "fix: cur frame " ++ show k ++ " = " ++ show c

        e <- empty (c /\ complement prev) -- we already know that prev is subset of c, check the full equality to detect fixpoint
        when (k > 0) $ do
            log Ic3Log $ "\tf" ++ show (k - 1) ++ (if e then " = " else " /= ") ++ "f" ++ show k ++ ":"
            log Ic3Log $ "\t\tf" ++ show (k - 1) ++ ": " ++ show prev
            log Ic3Log $ "\t\tf" ++ show  k      ++ ": " ++ show c
        when e $ throwE (Inv c)

        l <- isLastFrame
        unless l $ do
            log Ic3Log "fix': inductivity check over cubes blocked in the current frame"
            n <- getNextFrame
            ind' <- return . complement . joins . nub -- block unique
                <=< mapM (generalise c)               -- generalise
                <=< filterM (nonEmpty . (/\ n))       -- not blocked in next
                <=< filterM (   empty . (/\ post c))  -- not reachable in one step from current
                 $  map complement (conjuncts c)      -- blocked in current
            goFrameForth
            log Ic3Log $ "\tpush(f" ++ show k ++ ", f" ++ show (k + 1) ++ ", " ++ show ind' ++ ")"
            fix' c ind'

    generalise :: e 'BooleanSort -> e 'BooleanSort -> Ic3 a e (e 'BooleanSort)
    generalise s c = do
        log Ic3Log $ "generalise: performing assertions over the cube " ++ show c ++ " and the current frame"
        r1 <- local $ do
            -- Cube that is not in `s` nor in `post s`
            assert ((s \/ post s) /\ c)
            r' <- check
            showCheckResult ((s \/ post s) /\ c) r'
            return r'
        if r1
        then do
            r2 <- local $ do
                -- Cube that is in `s` but isn't in `post s`
                assert (post s /\ c)
                r' <- check
                showCheckResult (post s /\ c) r'
                return r'
            if r2
            then do
                let cs = conjuncts c

                fmap (either id (const c)) . runExceptT . forM (map meets . tail . subsequences $ cs) $ \c' -> do
                    r <- lift . local $ assert (post (s /\ complement c') /\ c') >> check
                    unless r $ throwE c'
            else local $ do
                assert (post s)
                uc <- unsatcore c
                log Ic3Log $ "unsat core: " ++ show uc
                return uc
        else local $ do
            assert (s \/ post s)
            uc <- unsatcore c
            log Ic3Log $ "unsat core: " ++ show uc
            return uc

    post s = prime s /\ flipPrime t
    pre  c = prime c /\ t

    showCheckResult :: e 'BooleanSort -> Bool -> Ic3 a e ()
    showCheckResult c r = do
        if r
        then do
            -- here, the operator @ represents "type application", which specifies explicit/concrete type arguments for a polymorphic function
            -- call of "mapMaybe" considers as Nothing those elements of the input list that cannot be successfully type-cast to VarF 'BooleanSort
            let arridxs = extractArrayIndexExpressions [c]
                vb      = mapMaybe (toStaticallySorted @ Var @ 'BooleanSort ) $ vars c
                vi      = mapMaybe (toStaticallySorted @ Var @ 'IntegralSort) $ vars c
                vai     = map (\(arr, idx) -> (select arr idx)) arridxs
            mb <- mapM (model . embed) vb
            mi <- mapM (model . embed) vi
            mai <- mapM model vai
            let vmb = zip vb mb
            let vmi = zip vi mi
            let vmai = zip vai mai
            log Ic3Log $ "complete model: " ++ show vmb ++ " " ++ show vmi ++ " " ++ show vmai
        else do
            uc <- unsatcore c
            log Ic3Log $ "unsat core: " ++ show uc

    -- somehow extract the set of all expressions that are used as array element indexes in the given formula (we assume arrays of ints indexed by ints)
    extractArrayIndexExpressions :: [e 'BooleanSort] -> [(e ('ArraySort 'IntegralSort 'IntegralSort), e 'IntegralSort)]
    extractArrayIndexExpressions = nub . concatMap extractArrIdxExprs

    extractArrIdxExprs :: e 'BooleanSort -> [(e ('ArraySort 'IntegralSort 'IntegralSort), e 'IntegralSort)]
    extractArrIdxExprs = mapMaybe filterIntInt . accesses where
        filterIntInt :: DynamicallyIndexedArrayAccess f -> Maybe (e ('ArraySort 'IntegralSort 'IntegralSort), e 'IntegralSort)
        filterIntInt (DynamicallyIndexedArrayAccess aa) = do
            StaticallyIndexedArrayAccess (IT2 (a, i)) <- toStaticallySorted aa
            a' <- filterInt a
            return (a', i)

        filterInt :: DynamicallyValuedArrayAccess f 'IntegralSort -> Maybe (e ('ArraySort 'IntegralSort 'IntegralSort))
        filterInt (DynamicallyValuedArrayAccess aa) = do
            StaticallyValuedArrayAccess a <- toStaticallySorted aa
            return a
