import TreeEntropy
open TreeEntropy

-- The table is exactly tight at d = 4, r = 1/8: the two sides are equal natural numbers ...
example : (8 + 1) ^ (9 * 4) * 1 ^ 4 * (8 ^ 4) ^ 4 * (8 * 4) ^ (16 + 2 * 4)
    = (27 ^ 4) ^ 4 * (1 * 4 + 8) ^ (16 + 2 * 4) * 8 ^ (10 * 4) := by decide +kernel

-- ... so lowering the constant by one unit makes the entry false, and the kernel sees it.
example : ¬ NatIneq 4 1 8 (27 ^ 4 - 1) (8 ^ 4) := by decide +kernel

-- At degree 5 the right end 3/d with the unrelaxed constant fails (`tableA3` shows it holds
-- for every other degree 3..119): this is the one place where the refined range is used.
example : ¬ NatIneq 5 3 5 (27 ^ 4) (8 ^ 4) := by decide +kernel
