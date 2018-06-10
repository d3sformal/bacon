{-# LANGUAGE DataKinds
           , FlexibleContexts
           , RankNTypes
           , TypeOperators #-}

-- topic: very simple scheduler that uses a cyclic buffer
-- program contains: (1) loops over individual array elements, (2) several if-then-else statements where the branching conditions test (in-)equality of an element at the given index with a constant or variable of an integer type

-- we need quantified language for the property and maybe elsewhere too
import Data.Expression
import QIc3
import Pdr
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

prime = (`substitute` Substitution (\v -> case match v of { Just (Var n s) -> Just . inject $ Var (n ++ "'") s; _ -> Nothing }))

prev :: [ALia 'IntegralSort] -> [ALia 'IntegralSort] -> [(ALia 'IntegralSort, ALia 'IntegralSort)]
prev = flip zip

constant :: [(ALia 'IntegralSort, ALia 'IntegralSort)] -> [ALia 'IntegralSort] -> ALia 'BooleanSort
constant prev vs' = fromMaybe false (and <$> mapM (\v' -> (v' .=.) <$> v' `lookup` prev) vs')

frame :: [ALia 'IntegralSort] -> ALia 'BooleanSort -> ALia 'BooleanSort
frame vs f = let vs' = map prime vs in f .&. constant (prev vs vs') (vs' \\ map (\(IFix (Var v s)) -> inject (Var v s)) (mapMaybe toStaticallySorted (vars f)))

-- TODO vyresit nasledujici
    -- modelovani array size (dost vopruz)

-- all variables used in the system to be analyzed by IC3
vs  = map (DynamicallySorted SIntegralSort) [pc, tu, ts, m, k, n, cur] ++ [DynamicallySorted (SArraySort SIntegralSort SIntegralSort) a, DynamicallySorted (SArraySort SIntegralSort SIntegralSort) b]

-- Pre and Post state variables (of type Int)
-- program counter
pc    = var "pc"   :: ALia 'IntegralSort
pc'   = var "pc'"  :: ALia 'IntegralSort
-- time_unit
tu    = var "tu"   :: ALia 'IntegralSort
tu'   = var "tu'"  :: ALia 'IntegralSort
-- time_slice
ts    = var "ts"   :: ALia 'IntegralSort
ts'   = var "ts'"  :: ALia 'IntegralSort
-- max_int
m     = var "m"    :: ALia 'IntegralSort
m'    = var "m'"   :: ALia 'IntegralSort
-- index for arrays / loop counter
k     = var "k"    :: ALia 'IntegralSort
k'    = var "k'"   :: ALia 'IntegralSort
-- array length (N)
n     = var "n"    :: ALia 'IntegralSort
n'    = var "n'"   :: ALia 'IntegralSort
-- currently scheduled thread
cur   = var "cur"  :: ALia 'IntegralSort
cur'  = var "cur'" :: ALia 'IntegralSort

-- Pre and Post state variables (of type [Int])
a   = var "a"   :: ALia ('ArraySort 'IntegralSort 'IntegralSort)
a'  = var "a'"  :: ALia ('ArraySort 'IntegralSort 'IntegralSort)
b   = var "b"   :: ALia ('ArraySort 'IntegralSort 'IntegralSort)
b'  = var "b'"  :: ALia ('ArraySort 'IntegralSort 'IntegralSort)

-- TODO
-- zpusob jak muzu kodovat for-loops ve transition relation: udelat backjump na mensi "pc" ktere odpovida "head" (viz Sorts.hs)
-- transition relation musi byt complete (prechod ze kazdeho stavu, treba ve forme self-loop do stejneho program counter)

-- TODO pridat frame conditions ke kazdemu disjunktu T (napr. ts' = ts pokud se ts nemeni)
	-- frame <var list> <formule>
	-- frame vs <formule>
	-- obcas muzu potrebovat jen sublist promennych
		-- nejspis definovat rucne: vs = [ pc, d, h, p, b, f, i, x, k1, k2, ak1, ak2 ]

-- initial state
i =
  --	time_unit = 1;
  --	time_slice = 20;
  --	max_int = 32767;
  --	int[] a = new int[N];
  --	int[] b = new int[N];
  pc .=. cnst 0 .&. tu .=. cnst 1 .&. ts .=. cnst 20 .&. m .=. cnst 32767 .&. k .=. cnst 0

-- transition relation
t =
  --	for (k = 0...N-1) a[k] = time_slice
  pc .=. cnst 0 .&. pc' .=. cnst 0 .&. k .<.  n .&. k' .=. k .+. cnst 1 .&. a' .=. store a k ts .|.
  pc .=. cnst 0 .&. pc' .=. cnst 1 .&. k .>=. n .&. k' .=. cnst 0 .|.

  --	for (k = 0...N-1) b[k] = max_int
  pc .=. cnst 1 .&. pc' .=. cnst 1 .&. k .<.  n .&. k' .=. k .+. cnst 1 .&. b' .=. store b k m .|.
  pc .=. cnst 1 .&. pc' .=. cnst 2 .&. k .>=. n .|.

  --	cur = 0
  pc .=. cnst 2 .&. pc' .=. cnst 3 .&. cur' .=. cnst 0 .|.

  --	while (true) do
  --		a[cur] -= time_unit
  pc .=. cnst 3 .&. pc' .=. cnst 4 .&. a' .=. store a cur (select a cur .+. (cnst (-1) .*. tu)) .&. k' .=. cnst 0 .|.

  --		for (k = 0...N-1) do
  --			if (k != cur) then b[k] += time_unit
  pc .=. cnst 4 .&. pc' .=. cnst 4 .&. k .<.  n .&. k ./=. cur .&. k' .=. k .+. cnst 1 .&. b' .=. store b k (select b k .+. tu) .|.
  pc .=. cnst 4 .&. pc' .=. cnst 4 .&. k .<.  n .&. k .=.  cur .&. k' .=. k .+. cnst 1 .|.

  --		end for
  --		if (a[cur] <= 0) then
  pc .=. cnst 4 .&. pc' .=. cnst 5 .&. k .>=. n .&. select a cur .<=. cnst 0 .|.
  pc .=. cnst 4 .&. pc' .=. cnst 6 .&. k .>=. n .&. select a cur .>.  cnst 0 .|.

  --			b[cur] = 0
  --			cur = cur + 1
  --			if (cur >= N) cur = 0
  --			b[cur] = 0
  --		end if
  pc .=. cnst 5 .&. pc' .=. cnst 6 .&. cur .+. cnst 1 .>=. n .&. b' .=. store (store b cur (cnst 0)) (cnst 0) (cnst 0) .&. cur' .=. cnst 0 .|.
  pc .=. cnst 5 .&. pc' .=. cnst 6 .&. cur .+. cnst 1 .<.  n .&. b' .=. store (store b cur (cnst 0)) cur' (cnst 0) .&. cur' .=. cur .+. cnst 1 .|.

  --		for (k = 0...N-1) do
  --			if (a[k] <= 0) then a[k] = time_slice
  --		end for
  --	end while
  pc .=. cnst 6 .&. pc' .=. cnst 6 .&. k .<.  n .&. a' .=. store a k ts .&. k' .=. k .+. cnst 1 .|.
  pc .=. cnst 6 .&. pc' .=. cnst 3 .&. k .>=. n

-- check expected outcome
cex :: Show (e 'BooleanSort) => Either (Cex e) (Inv e) -> IO ()
cex (Left  (Cex cs)) = putStrLn . ("succeeded with counterexample: " ++) . show $ cs
cex (Right (Inv iv)) = error    . ("failed with invariant: "         ++) . show $ iv

inv :: Show (e 'BooleanSort) => Either (Cex e) (Inv e) -> IO ()
inv (Left  (Cex cs)) = error    . ("failed with counterexample: " ++) . show $ cs
inv (Right (Inv iv)) = putStrLn . ("succeeded with invariant: "   ++) . show $ iv

-- TODO upravit seznam auxiliary variables tak aby odpovidal moji property
-- auxiliary variables for quantified property
k, l :: forall g. VarF :<: g => IFix g 'IntegralSort
k = var "k"
l = var "l"

-- TODO zakodovat skutecnou property
-- run IC3 with different properties, check whether IC3 responds with an expected Cex or Inv
main = mapM_ (\(sink, i, p) -> sink =<< runSolver logAll ( ic3 vs i t p )) [ (inv, pc .=. cnst 0 .&. i ./=. j .&. i .>=. cnst 0 .&. j .>=. cnst 0, pc .=. cnst 3 .->. exists [k, l] (k ./=. l .&.  select a k .=.  select a l))
                                                                           , (cex, pc .=. cnst 0 .&. i ./=. j .&. i .>=. cnst 0 .&. j .>=. cnst 0, pc .=. cnst 3 .->. forall [k, l] (k ./=. l .->. select a k ./=. select a l)) ]
                                                                           -- , (cex, pc .=. cnst 0 .&.              i .>=. cnst 0 .&. j .>=. cnst 0, pc .=. cnst 3 .->. exists [k, l] (k ./=. l .&.  select a k .=.  select a l)) ]
