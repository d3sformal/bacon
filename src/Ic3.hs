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
           , TypeOperators
           , UndecidableInstances #-}

module Ic3 where

import Algebra.Lattice
import Control.Arrow
import Control.Lens hiding ((%~), pre)
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Control.Zipper
import Data.Expression
import Data.List hiding (and, or, init)
import Data.Maybe
import Data.Typeable
import Prelude hiding (and, or, not, log, init)

import Pdr
import Solver

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

getPredicates :: Ic3 a e [e 'BooleanSort]
getPredicates = lift $ use predicates

addPredicates :: Eq (e 'BooleanSort) => [e 'BooleanSort] -> Ic3 a e ()
addPredicates ps = lift $ predicates %= nub . (++ ps)

data Ic3Log = Ic3Log deriving ( Eq, Typeable )

logIc3 :: Typeable b => b -> Bool
logIc3 = logExactly Ic3Log

ic3 :: forall e f. ( ComplementedLattice (e 'BooleanSort)
                   , MonadSolver e (Solver e)
                   , Show (e 'BooleanSort)
                   , Eq (e 'BooleanSort)
                   , e ~ IFix f
                   , VarF :<: f
                   , EqualityF :<: f
                   , ConjunctionF :<: f
                   , DisjunctionF :<: f
                   , IEq1 f
                   , IShow f )
    => [DynamicallySorted f]
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
            bs <- enumerate (i /\ complement p)
            unless (null bs) $ throwE (Cex [head bs])

    bad :: Ic3 Cex e ()
    bad = do
        -- check post(top frame) /\ not prop
        n  <- getCurrentFrameNum
        log Ic3Log $ "iter" ++ show n ++ ":"
        bad'

    bad' :: Ic3 Cex e ()
    bad' = do
        c  <- getCurrentFrame
        n  <- getCurrentFrameNum
        bs <- enumerate (post c /\ complement p)
        unless (null bs) $ do
            log Ic3Log $ "\tpost(f" ++ show n ++ "): " ++ show (post c) ++ "\n"
            catchE (mapM_ (block []) bs) $ \(Cex trace) -> do
                let trace' = zipWith ($) (iterate (prime .) id) (map (/\ t) (P.init trace) ++ [last trace])
                log Ic3Log "\tabs cex: "
                mapM_ (log Ic3Log . ("\t\t" ++) . show) trace'
                log Ic3Log ""
                r <- nonEmpty (meets trace')
                if r then throwE . Cex =<< concretise trace'
                else do
                    is <- concatMap (literals . unprime) <$> interpolate trace'
                    log Ic3Log "\trefine: "
                    mapM_ (log Ic3Log . ("\t\t" ++) . show) is
                    addPredicates is
                    ps <- getPredicates
                    log Ic3Log $ "\tpredicates: " ++ show (length ps)
                    log Ic3Log ""
                    goToLastFrame
            bad'

    empty :: e 'BooleanSort -> Ic3 a e Bool
    empty s = P.not <$> nonEmpty s

    nonEmpty :: e 'BooleanSort -> Ic3 a e Bool
    nonEmpty s = local $ assert s >> check

    enumerate :: e 'BooleanSort -> Ic3 a e [e 'BooleanSort]
    enumerate s = local $ assert s >> enumerate'

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

    concretise :: [e 'BooleanSort] -> Ic3 a e [e 'BooleanSort]
    concretise tr = local $ do
        assert (meets tr)

        forM [0 .. length tr - 1] $ \s -> do
            let bs = mapMaybe toStaticallySorted vs :: [e 'BooleanSort]
                is = mapMaybe toStaticallySorted vs :: [e 'IntegralSort]

            a <- fmap meets . forM bs $ \v -> model (prime' s v) >>= \b -> if b == top then return v else return (complement v)
            b <- fmap meets . forM is $ \v -> (v .=.) <$> model (prime' s v)

            return (a /\ b)

    cube :: Ic3 a e (e 'BooleanSort)
    cube = do
        ps <- getPredicates
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
        pbs <- enumerate (c /\ pre b)

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
                    s   <- generalise (c'' \/ post c'') b'
                    log Ic3Log $ "\tf0" ++ (if n == 0 then "" else if n == 1 then ", f1" else if n == 2 then ", f1, f2" else  ", ..., f" ++ show n) ++ " \\ " ++ show s
                    blockHenceBack s

    blockHenceBack :: e 'BooleanSort -> Ic3 a e ()
    blockHenceBack s = do
        bot <- isFirstFrame
        modifyFrame (/\ complement s)
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

        e <- empty (c /\ complement prev) -- we already know that prev is subset of c, check the full equality to detect fixpoint
        when (k > 0) $ do
            log Ic3Log $ "\tf" ++ show (k - 1) ++ (if e then " = " else " /= ") ++ "f" ++ show k ++ ":"
            log Ic3Log $ "\t\tf" ++ show (k - 1) ++ ": " ++ show prev
            log Ic3Log $ "\t\tf" ++ show  k      ++ ": " ++ show c
        when e $ throwE (Inv c)

        l <- isLastFrame
        unless l $ do
            n <- getNextFrame
            ind' <- return . complement . joins . nub -- block unique
                <=< mapM (generalise (c \/ post c))   -- generalise
                <=< filterM (nonEmpty . (/\ n))       -- not blocked in next
                <=< filterM (   empty . (/\ post c))  -- not reachable in one step from current
                 $  map complement (conjuncts c)      -- blocked in current
            goFrameForth
            log Ic3Log $ "\tpush(f" ++ show k ++ ", f" ++ show (k + 1) ++ ", " ++ show ind' ++ ")"
            fix' c ind'

    generalise s c = local $ assert s >> unsatcore c

    post s = prime s /\ flipPrime t
    pre  c = prime c /\ t
