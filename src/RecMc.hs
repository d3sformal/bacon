{-# LANGUAGE DataKinds
           , DuplicateRecordFields
           , FlexibleContexts
           , GADTs
           , KindSignatures
           , MonadComprehensions
           , RankNTypes
           , ScopedTypeVariables
           , TemplateHaskell
           , TypeOperators
           , UndecidableInstances #-}

module RecMc where

import Algebra.Lattice
import Control.Lens hiding (over, under, to, imap)
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.List
import Control.Monad.Trans.State
import Data.Either
import Data.List hiding (insert, init)
import Data.Map hiding (map, mapMaybe, filter, (\\))
import Data.Maybe
import Data.Monoid
import Expression
import Prelude hiding (init, abs, log)

import qualified Prelude as P

import Pdr hiding (Cex, Inv)
import Solver

import qualified Pdr

type FunctionName = String

newtype Cex e = Cex [(FunctionName, e 'BooleanSort)]
newtype Inv e = Inv (Map FunctionName (e 'BooleanSort))

instance Show (e 'BooleanSort) => Show (Cex e) where
    show (Cex es) = "cex: " ++ show es

instance Show (e 'BooleanSort) => Show (Inv e) where
    show (Inv s) = "inv: " ++ show s

data Query    e = Query Int FunctionName (e 'BooleanSort) (e 'BooleanSort)
data Call     f = Call { functionName :: FunctionName, placeHolder :: IFix f 'BooleanSort, arguments :: Substitution f }
data Function f = Function { functionName :: FunctionName
                           , inputs       :: [DynamicallySorted f]
                           , locals       :: [DynamicallySorted f]
                           , outputs      :: [DynamicallySorted f]
                           , entry        :: IFix f 'BooleanSort
                           , transition   :: IFix f 'BooleanSort
                           , exit         :: IFix f 'BooleanSort
                           , calls        :: [Call f] }

data RecMcState e = RecMcState { _depth              :: Int
                               , _queries            :: [Query e]
                               , _functions          :: [FunctionName]
                               , _underapproximation :: Map Int (Map FunctionName (e 'BooleanSort))
                               , _overapproximation  :: Map Int (Map FunctionName (e 'BooleanSort)) }

makeLenses ''RecMcState

type RecMc r e a = ExceptT (r e) (StateT (RecMcState e) (Solver e)) a

getDepth :: RecMc a e Int
getDepth = lift $ use depth

incDepth :: ComplementedLattice (e 'BooleanSort) => RecMc a e Int
incDepth = do
    d <- getDepth

    fs <- getFunctions

    lift $ do
        depth              %= (+ 1)
        underapproximation %= insert (d + 1) (fromList $ zip fs $ repeat bottom)
        overapproximation  %= insert (d + 1) (fromList $ zip fs $ repeat top)

    return d

pushQuery :: Query e -> RecMc a e ()
pushQuery q = lift $ queries %= (q :)

popQueries :: (Query e -> RecMc a e Bool) -> RecMc a e ()
popQueries f = lift . (queries .=) =<< filterM (fmap P.not . f) =<< lift (use queries)

notDone :: RecMc a e Bool
notDone = lift $ P.not . P.null <$> use queries

getQuery :: RecMc a e (Query e)
getQuery = lift $ head <$> use queries

getFunctions :: RecMc a e [FunctionName]
getFunctions = lift $ use functions

getUnderapproximations :: Int -> RecMc a e (Map FunctionName (e 'BooleanSort))
getUnderapproximations d = lift $ (! d) <$> use underapproximation

getOverapproximations :: Int -> RecMc a e (Map FunctionName (e 'BooleanSort))
getOverapproximations d = lift $ (! d) <$> use overapproximation

addUnderapproximation :: JoinSemiLattice (e 'BooleanSort) => Int -> FunctionName -> e 'BooleanSort -> RecMc a e ()
addUnderapproximation d f u = lift $ underapproximation . ix d . ix f %= (\/ u)

addOverapproximation :: MeetSemiLattice (e 'BooleanSort) => Int -> FunctionName -> e 'BooleanSort -> RecMc a e ()
addOverapproximation d f o = lift $ overapproximation . ix d . ix f %= (/\ o)

recmc :: forall e f. ( ComplementedLattice (e 'BooleanSort)
                     , e ~ IFix f
                     , VarF                       :<: f
                     , ExistentialF 'BooleanSort  :<: f
                     , ExistentialF 'IntegralSort :<: f
                     , EqualityF                  :<: f
                     , IFunctor f
                     , IEq1 f
                     , IShow f )
      => ([DynamicallySorted f] -> e 'BooleanSort -> e 'BooleanSort -> e 'BooleanSort -> Solver e (Either (Pdr.Cex e) (Pdr.Inv e)))
      -> FunctionName
      -> e 'BooleanSort
      -> e 'BooleanSort
      -> Map FunctionName (Function f)
      -> (Solver e) (Either (Cex e) (Inv e))
recmc c m i p s = flip evalStateT (RecMcState 0 [] fs under over) . pdr $ Pdr init safe fix where
    fs = keys s

    under = fromList [(-1, fromList $ zip fs $ repeat bottom), (0, fromList $ zip fs $ repeat bottom)]
    over  = fromList [(-1, fromList $ zip fs $ repeat bottom), (0, fromList $ zip fs $ repeat top)]

    init = return ()
    safe = do
        d <- getDepth

        pushQuery $ Query d m i p
        safe'

    safe' = notDone >>= \n -> when n $ do
        Query b f i' p' <- getQuery
        log $ "query: " ++ f ++ "@" ++ show b ++ "\n"

        let fun@(Function _ is ls os _ t _ cs) = s ! f
            vs = is ++ ls ++ os

        tu <- transitions t cs <$> getUnderapproximations (b - 1)
        ru <- lift . lift $ c vs i' tu p'
        case ru of
            Left  (Pdr.Cex cexu) -> do
                newU <- eliminateVars ls =<< abstractionFromCounterexample fun tu cexu i' p'
                log $ "falsified: yes, new underapproximation of " ++ f ++ "@" ++ show b ++ ": " ++ show newU ++ "\n"
                addUnderapproximation b f newU
                popQueries $ \(Query b' f' i'' p'') -> if f /= f' then return False else do
                    admitsWitness     <- realised (head cexu /\ i'')
                    containsViolation <- realised (last cexu /\ complement p'')
                    return $ b' >= b && admitsWitness && containsViolation
            Right (Pdr.Inv _) -> do
                log "falsified: no\n"
                to <- transitions t cs <$> getOverapproximations (b - 1)
                ro <- lift . lift $ c vs i' to p'
                case ro of
                    Right (Pdr.Inv invo) -> do
                        newO <- eliminateVars ls =<< abstractionFromInvariant fun invo
                        log $ "proven: yes, new overapproximation of " ++ f ++ "@" ++ show b ++ ": " ++ show newO ++ "\n"
                        addOverapproximation b f newO
                        popQueries $ \(Query b' f' i'' p'') -> if f /= f' then return False else do
                            subsumesInitial <- notRealised (complement invo /\ i'')
                            ensuresProperty <- notRealised (invo /\ complement p'')
                            return $ b' <= b && subsumesInitial && ensuresProperty
                    Left  (Pdr.Cex cexo) -> do
                        log "proven: no\n"
                        mapM_ pushQuery =<< cuts b f cexo i' p'
        safe'

    realised    e = local $ assert e >> check
    notRealised e = P.not <$> realised e

    abstractionFromCounterexample (Function _ is ls os _ _ _ _) t cs i' p' = do
        let tr  = foldPath i' (take (length cs - 1) $ iterate prime t) (complement p')
            vs  = concat $ zipWith ($) ps' (replicate (length cs - 1) (is ++ ls ++ os))
            ps' = iterate (map (\(DynamicallySorted es e) -> DynamicallySorted es (prime e)) .) id
        unprime <$> eliminateVars ((vs \\ is) \\ (ps' !! (length cs - 1)) os) tr

    abstractionFromInvariant (Function _ _ ls os en _ ex _) inv = do
        i' <- unprime <$> eliminateVars (ls ++ os) (inv /\ en)
        p' <- unprime <$> eliminateVars ls (inv /\ ex)
        return (complement i' \/ p')

    prime :: forall s. e s -> e s
    prime = (`substitute` Substitution (\v -> case match v of { Just (Var n vs) -> Just . inject $ Var (n ++ "'") vs; _ -> Nothing }))

    foldPath :: e 'BooleanSort -> [e 'BooleanSort] -> e 'BooleanSort -> e 'BooleanSort
    foldPath _ [] _ = error "trying to fold an empty path"
    foldPath i' (t : ts) p' = meets $ zipWith ($) (iterate (prime .) id) ((i' /\ t) : ts ++ [p'])

    unprime :: forall s. e s -> e s
    unprime = (`substitute` Substitution (\v -> case match v of { Just (Var n vs) -> Just . inject $ Var (filter (/= '\'') n) vs; _ -> Nothing }))

    eliminateVars vs f = do
        let bs = mapMaybe toStaticallySorted vs :: [e 'BooleanSort]
            is = mapMaybe toStaticallySorted vs :: [e 'IntegralSort]

        eliminate . exists (map transcode bs) . exists (map transcode is) $ f

    transcode e = case match e of
        Just (Var n vs) -> inject $ Var n vs
        _               -> error "transcoding non-variable"

    transitions t cs abs = t `substitute` mconcat (map (\(Call f ph sub) -> (abs ! f `substitute` sub) `for` ph) cs)

    cuts b f tr i' p' = runListT [ Query (b - 1) f' i'' p'' | sp <- splits tr, (f', i'', p'') <- call sp ] where
        splits as = ListT . return . P.init . tail $ splits' as []
        splits' []           r = [([], reverse r)]
        splits' as@(a : as') r = (reverse r, as) : splits' as' (a : r)

        call (prefix, suffix) = do
            let e1  = last prefix
                e2  = head suffix
                fun = s ! f
                vs  = inputs fun ++ locals fun ++ outputs fun
                t   = transition fun
                cs  = calls fun

            Call f' ph sub <- ListT . return $ cs

            guard =<< lift (notRealised (e1 /\ t /\ complement ph /\ prime e2))

            u <- lift $ getUnderapproximations (b - 1)
            o <- lift $ getOverapproximations  (b - 1)

            let tu = transitions t cs u
                to = transitions t cs o

                upath = foldPath i' (replicate (length prefix - 1) to ++ replicate (length suffix) tu) (complement p')
                opath = foldPath i' (replicate (length prefix) to ++ replicate (length suffix - 1) tu) (complement p')
                rpath = foldPath i' (replicate (length prefix - 1) to ++ [t `substitute` ((ibound /\ obound) `for` ph)] ++ replicate (length suffix - 1) tu) (complement p')

                is = inputs  (s ! f')
                os = outputs (s ! f')
                en = entry   (s ! f')
                ex = exit    (s ! f')

                ibound = meets $ map (\(DynamicallySorted ivs iv) -> inject $ Equals ivs iv (iv `substitute` sub)) is
                obound = meets $ map (\(DynamicallySorted ovs ov) -> inject $ Equals ovs ov (ov `substitute` sub)) os

                ps' = iterate (map (\(DynamicallySorted es e) -> DynamicallySorted es (prime e)) .) id

            guard =<< lift (notRealised upath)
            guard =<< lift (   realised opath)

            p'' <- lift $ unprime <$> eliminateVars (concat (take (length tr) (map ($ vs) ps')) \\ (ps' !! length prefix) (is ++ os)) rpath

            return (f', en, complement ex \/ complement p'')

    fix = do
        d  <- incDepth

        log "push summary:"
        forM_ [0 .. d - 1] $ \b -> mapM_ (pushInductive b) fs
        log ""

        r <- P.and <$> mapM (isInductive d) fs
        if r then do
            log "inductive: yes\n"
            throwE . Inv =<< getOverapproximations d
        else log "inductive: no\n"

    isInductive b f = do
        (vs, i', t, p') <- inductivityQuery b f
        isRight <$> (lift . lift $ c vs i' t p')

    inductivityQuery b f = do
        abs <- getOverapproximations b

        let Function _ is ls os en t ex cs = s ! f
            to = transitions t cs abs

        return (is ++ ls ++ os, en, to, complement ex \/ abs ! f)

    pushInductive b f = do
        r <- isInductive b f
        when r $ do
            log $ "\t" ++ f ++ "@" ++ show b ++ "\n"
            addOverapproximation (b + 1) f . (! f) =<< getOverapproximations b

