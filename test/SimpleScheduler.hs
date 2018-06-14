{-# LANGUAGE DataKinds
           , FlexibleContexts
           , FlexibleInstances
           , RankNTypes
           , TypeOperators
           , TypeSynonymInstances #-}

-- topic: very simple scheduler that uses a cyclic buffer
-- program contains: (1) loops over individual array elements, (2) several if-then-else statements where the branching conditions test (in-)equality of an element at the given index with a constant or variable of an integer type

-- we need quantified language for the property and maybe elsewhere too
import Data.Expression
import Data.List hiding (and)
import Data.Maybe
import Data.Singletons
import QIc3
import Pdr
import Prelude hiding (and)
import Solver

-- complete program in C-like syntax
--   time_unit = 1;
--   time_slice = 20;
--   max_int = 32767;
--   // elements of array 'a': remaining time slice (in the current round)
--   int[] a = new int[N};
--   // elements of array 'b': jak dlouho uz proces/vlakno nebezel
--   int[] b = new int[N];
--   // init phase
--   for (k = 0...N-1) a[k] = time_slice
--   for (k = 0...N-1) b[k] = max_int
--   cur = 0
--   // scheduler loop (infinite)
--   while (true) do
--     a[cur] -= time_unit // current thread used (run for) one time step
--     for (k = 0...N-1) do
--       if (k != cur) then b[k] += time_unit // other threads did not run for another time step
--     end for
--     // change current thread
--     if (a[cur] <= 0) then
--       b[cur] = 0 // thread just finished its round
--       cur = cur + 1
--       if (cur >= N) then cur = 0
--       b[cur] = 0 // thread will run just now
--     end if
--     // prepare for the next round
--     for (k = 0...N-1) do
--       if (a[k] <= 0) then a[k] = time_slice
--     end for
--   end while

-- several functions that enable definition of "frame" (set of variables not modified by a specific disjunct of the transition relation)

prime = flip substitute (Substitution f) where
    f v = case match v of
        Just (Var n s) -> Just . inject $ Var (n ++ "'") s
        _              -> Nothing

lookupPre :: Eq b => [a] -> [b] -> b -> Maybe a
lookupPre pres posts = flip lookup $ zip posts pres

constant :: ( IEq1 f, IShow f, EqualityF :<: f, ConjunctionF :<: f, DisjunctionF :<: f, SingI s ) => (IFix f s -> Maybe (IFix f s)) -> [IFix f s] -> IFix f 'BooleanSort
constant pre vs' = inheritPreValuesOrFail where
    inheritPreValue  v'    = (v' .=.) <$> pre v'
    inheritPreValues       = and <$> mapM inheritPreValue vs'
    inheritPreValuesOrFail = fromMaybe (error $ "could not frame all variables in " ++ show vs') inheritPreValues

frameMonoSort :: SingI s => [ALia s] -> ALia 'BooleanSort -> ALia 'BooleanSort
frameMonoSort all f = f .&. constant (lookupPre all all') unconstrained where
    bound         = mapMaybe toStaticallySorted $ vars f
    all'          = map prime all
    unconstrained = all' \\ map toALia bound

    toALia (IFix (Var v s)) = inject $ Var v s

frame :: ALia 'BooleanSort -> ALia 'BooleanSort
frame = frameMonoSort ss . frameMonoSort as where
    as :: [ALia ('ArraySort 'IntegralSort 'IntegralSort)]
    as = mapMaybe toStaticallySorted schedvs

    ss :: [ALia 'IntegralSort]
    ss = mapMaybe toStaticallySorted schedvs

-- all variables used in the system to be analyzed by IC3
scalarvn = [pc, tu, ts, m, k, n, cur]
arrayvn  = [a, b]
schedvs  = map toDynamicallySorted scalarvn ++ map toDynamicallySorted arrayvn

-- Pre and Post state variables (of type Int)
-- program counter
pc   = var "pc"   :: ALia 'IntegralSort
pc'  = var "pc'"  :: ALia 'IntegralSort
-- time_unit
tu   = var "tu"   :: ALia 'IntegralSort
tu'  = var "tu'"  :: ALia 'IntegralSort
-- time_slice
ts   = var "ts"   :: ALia 'IntegralSort
ts'  = var "ts'"  :: ALia 'IntegralSort
-- max_int
m    = var "m"    :: ALia 'IntegralSort
m'   = var "m'"   :: ALia 'IntegralSort
-- index for arrays / loop counter
k    = var "k"    :: ALia 'IntegralSort
k'   = var "k'"   :: ALia 'IntegralSort
-- array length (N)
n    = var "n"    :: ALia 'IntegralSort
n'   = var "n'"   :: ALia 'IntegralSort
-- currently scheduled thread
cur  = var "cur"  :: ALia 'IntegralSort
cur' = var "cur'" :: ALia 'IntegralSort

-- Pre and Post state variables (of type [Int])
a  = var "a"  :: ALia ('ArraySort 'IntegralSort 'IntegralSort)
a' = var "a'" :: ALia ('ArraySort 'IntegralSort 'IntegralSort)
b  = var "b"  :: ALia ('ArraySort 'IntegralSort 'IntegralSort)
b' = var "b'" :: ALia ('ArraySort 'IntegralSort 'IntegralSort)

-- initial state
schedi =
  --	time_unit = 1;
  --	time_slice = 20;
  --	max_int = 32767;
  --	int[] a = new int[N];
  --	int[] b = new int[N];
  pc .=. 0 .&. tu .=. 1 .&. ts .=. 20 .&. m .=. 32767 .&. k .=. 0 .&. n .>. 0

-- we model the array size through the symbolic variable n used as the upper bound for array indexes within loops
    -- the variable n is just constrained to be greater than 0 (i.e., array sizes can be completely arbitrary, but we do not want to try proving the given property for arrays with a negative size)
    -- if this simple approach is not sufficient then we can use an uninterpreted function (encoded by an array) that captures the array lengths, i.e. f(a) = a_length
    -- anyway, we have to manually reflect the array length in the interpretation of statements and properties: for example, instead of "[forall i. p(a(i))]" use something like "[forall i. 0 <= i < f(a) implies p(a(i))]"

-- transition relation
    -- it has to be complete, i.e. we must define transition from every state
    -- one approach is to create self-loops (to the same program counter)
    -- frame condition has to be defined for each disjunct (to capture all unmodified state variables)
schedt =
  --	for (k = 0...N-1) a[k] = time_slice
  frame ( pc .=. 0 .&. pc' .=. 0 .&. k .<.  n .&. k' .=. k .+. 1 .&. a' .=. store a k ts ) .|.
  frame ( pc .=. 0 .&. pc' .=. 1 .&. k .>=. n .&. k' .=. 0 ) .|.

  --	for (k = 0...N-1) b[k] = max_int
  frame ( pc .=. 1 .&. pc' .=. 1 .&. k .<.  n .&. k' .=. k .+. 1 .&. b' .=. store b k m ) .|.
  frame ( pc .=. 1 .&. pc' .=. 2 .&. k .>=. n ) .|.

  --	cur = 0
  frame ( pc .=. 2 .&. pc' .=. 3 .&. cur' .=. 0 ) .|.

  --	while (true) do
  --		a[cur] -= time_unit
  frame ( pc .=. 3 .&. pc' .=. 4 .&. a' .=. store a cur (select a cur .+. negate tu) .&. k' .=. 0 ) .|.

  --		for (k = 0...N-1) do
  --			if (k != cur) then b[k] += time_unit
  frame ( pc .=. 4 .&. pc' .=. 4 .&. k .<.  n .&. k ./=. cur .&. k' .=. k .+. 1 .&. b' .=. store b k (select b k .+. tu) ) .|.
  frame ( pc .=. 4 .&. pc' .=. 4 .&. k .<.  n .&. k .=.  cur .&. k' .=. k .+. 1 ) .|.

  --		end for
  --		if (a[cur] <= 0) then
  frame ( pc .=. 4 .&. pc' .=. 5 .&. k .>=. n .&. select a cur .<=. 0 ) .|.
  frame ( pc .=. 4 .&. pc' .=. 6 .&. k .>=. n .&. select a cur .>.  0 .&. k' .=. 0 ) .|.

  --			b[cur] = 0
  --			cur = cur + 1
  --			if (cur >= N) cur = 0
  --			b[cur] = 0
  --		end if
  frame ( pc .=. 5 .&. pc' .=. 6 .&. cur .+. 1 .>=. n .&. b' .=. store (store b cur 0) cur' 0 .&. cur' .=. 0         .&. k' .=. 0 ) .|.
  frame ( pc .=. 5 .&. pc' .=. 6 .&. cur .+. 1 .<.  n .&. b' .=. store (store b cur 0) cur' 0 .&. cur' .=. cur .+. 1 .&. k' .=. 0 ) .|.

  --		for (k = 0...N-1) do
  --			if (a[k] <= 0) then a[k] = time_slice
  --		end for
  --	end while
  frame ( pc .=. 6 .&. pc' .=. 6 .&. k .<.  n .&. a' .=. store a k ts .&. k' .=. k .+. 1 ) .|.
  frame ( pc .=. 6 .&. pc' .=. 3 .&. k .>=. n )

-- check expected outcome
cex :: Show (e 'BooleanSort) => Either (Cex e) (Inv e) -> IO ()
cex (Left  (Cex cs)) = putStrLn . ("succeeded with counterexample: " ++) . show $ cs
cex (Right (Inv iv)) = error    . ("failed with invariant: "         ++) . show $ iv

inv :: Show (e 'BooleanSort) => Either (Cex e) (Inv e) -> IO ()
inv (Left  (Cex cs)) = error    . ("failed with counterexample: " ++) . show $ cs
inv (Right (Inv iv)) = putStrLn . ("succeeded with invariant: "   ++) . show $ iv

-- auxiliary variables for quantified property
i, j :: forall g. VarF :<: g => IFix g 'IntegralSort
i = var "i"
j = var "j"

-- quantified property over the array content defined using the template "forall i,j @ P(i,j)"
    -- what it says: a thread further away from the current thread in the cyclic buffer did not run for a longer time
    -- plain text encoding: forall i,j @ ((i >= 0 and i < n and j >= 0 and j < n) and ((i >= cur and j <= cur) or (i >= cur and j >= i) or (i <= cur and j <= cur and j >= i))) => (b[i] <= b[j])
schedp =
    pc .=. 3 .->. forall [i, j] ( ( 0 .<=. i .&. i .<. n .&.
                                    0 .<=. j .&. j .<. n .&.
                                    ( (   j .<=. cur .&. cur .<=. i   ) .|.
                                      ( cur .<=. i   .&.   i .<=. j   ) .|.
                                      (   i .<=. j   .&.   j .<=. cur ) ) ) .->. ( select b i .<=. select b j ) )

-- run IC3 with different properties, check whether IC3 responds with an expected Cex or Inv
main = inv =<< runSolver logAll ( ic3 schedvs schedi schedt schedp )


-- allow use of integer literals directly without the need to prefix them with "cnst"
instance Num (ALia 'IntegralSort) where
    fromInteger = cnst . fromIntegral

    a + b = a .+. b
    a - b = a .+. negate b
    a * b = a .*. b

    negate a = cnst (-1) * a

    abs    a = ite (a .>=. cnst 0) a (negate a)
    signum a =
        ite (a .>. cnst 0)
            (cnst 1)
            (ite (a .<. cnst 0)
                 (cnst (-1))
                 (cnst 0))
