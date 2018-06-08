{-# LANGUAGE DataKinds
           , FlexibleContexts
           , RankNTypes
           , TypeOperators #-}

-- topic: very simple scheduler that uses a cyclic buffer
-- program contains: (1) loops over individual array elements, (2) several if-then-else statements where the branching conditions test (in-)equality of an element at the given index with a constant or variable of an integer type

import Data.Expression
import Ic3 -- we do not use quantifiers intentionally
import Pdr
import Solver

-- TODO zakodovani: rozsiruju soubor bacon/test/DuplicateEntry.hs
--	obsahuje taky priklad jak zadefinovat pole
--	zpusob jak muzu kodovat for-loops ve transition relation: udelat backjump na mensi "pc" ktere odpovida "head" (viz Sorts.hs)
--	transition relation musi byt complete (prechod ze kazdeho stavu, treba ve forme self-loop do stejneho program counter)

-- TODO fragmenty zdrojaku
--	time_unit = 1;
--	time_slice = 20;
--	max_int = 32767;
--	// elements of array 'a': remaining time slice (in the current round)
--	int[] a = new int[N};
--	// elements of array 'b': jak dlouho uz proces/vlakno nebezel
--	int[] b = new int[N];
--	// init phase
--	for (k = 0...N-1) a[k] = time_slice
--	for (k = 0...N-1) b[k] = max_int
--	// scheduler loop (infinite)
--	while (true) do
--		a[cur] -= time_unit // current thread used (run for) one time step
--		for (k = 0...N-1) do
--			if (k != cur) then b[k] += time_unit // other threads did not run for another time step
--		end for
--		// change current thread
--		if (a[cur] <= 0) then
--			b[cur] = 0 // thread just finished its round
--			cur = cur + 1
--			if (cur >= N) cur = 0
--			b[cur] = 0 // thread will run just now
--		end if
--		// prepare for the next round
--		for (k = 0...N-1) do
--			if (a[k] <= 0) then a[k] = time_slice
--		end for
--	end while
-- TODO end





-- All variables used in the system to be analyzed by IC3
vs  = map (DynamicallySorted SIntegralSort) [pc, i, j, v] ++ [DynamicallySorted (SArraySort SIntegralSort SIntegralSort) a]

-- Pre and Post state variables (of type Int)
pc  = var "pc"  :: ALia 'IntegralSort
pc' = var "pc'" :: ALia 'IntegralSort
i   = var "i"   :: ALia 'IntegralSort
i'  = var "i'"  :: ALia 'IntegralSort
j   = var "j"   :: ALia 'IntegralSort
j'  = var "j'"  :: ALia 'IntegralSort
v   = var "v"   :: ALia 'IntegralSort
v'  = var "v'"  :: ALia 'IntegralSort

-- Pre and Post state variables (of type [Int])
a   = var "a"   :: ALia ('ArraySort 'IntegralSort 'IntegralSort)
a'  = var "a'"  :: ALia ('ArraySort 'IntegralSort 'IntegralSort)

-- The transition relation
t = pc .=. cnst 0 .&. pc' .=. cnst 1 .&. i' .=. i .&. j' .=. j .&. v' .=. select a i .&. a' .=. a .|.
    pc .=. cnst 1 .&. pc' .=. cnst 2 .&. i' .=. i .&. j' .=. j .&. v' .=. v .&. a' .=. store a j v .|.
    pc .=. cnst 2 .&. pc' .=. cnst 2 .&. i' .=. i .&. j' .=. j .&. v' .=. v .&. a' .=. a

-- Check expected outcome
cex :: Show (e 'BooleanSort) => Either (Cex e) (Inv e) -> IO ()
cex (Left  (Cex cs)) = putStrLn . ("succeeded with counterexample: " ++) . show $ cs
cex (Right (Inv iv)) = error    . ("failed with invariant: "         ++) . show $ iv

inv :: Show (e 'BooleanSort) => Either (Cex e) (Inv e) -> IO ()
inv (Left  (Cex cs)) = error    . ("failed with counterexample: " ++) . show $ cs
inv (Right (Inv iv)) = putStrLn . ("succeeded with invariant: "   ++) . show $ iv

-- Auxiliary variables for quantified property
k, l :: forall g. VarF :<: g => IFix g 'IntegralSort
k = var "k"
l = var "l"

-- Run ic3 with different properties, check whether ic3 responds with an expected Cex or Inv
main = mapM_ (\(sink, i, p) -> sink =<< runSolver logAll ( ic3 vs i t p )) [ (inv, pc .=. cnst 0 .&. i ./=. j .&. i .>=. cnst 0 .&. j .>=. cnst 0, pc .=. cnst 2 .->. exists [k, l] (k ./=. l .&.  select a k .=.  select a l))
                                                                           , (cex, pc .=. cnst 0 .&. i ./=. j .&. i .>=. cnst 0 .&. j .>=. cnst 0, pc .=. cnst 2 .->. forall [k, l] (k ./=. l .->. select a k ./=. select a l)) ]
                                                                           -- , (cex, pc .=. cnst 0 .&.              i .>=. cnst 0 .&. j .>=. cnst 0, pc .=. cnst 2 .->. exists [k, l] (k ./=. l .&.  select a k .=.  select a l)) ]
