import TreeEntropy
open TreeEntropy

-- This file must NOT compile: the claim is false and `decide +kernel` has to reject it.
example : NatIneq 4 1 8 (27 ^ 4 - 1) (8 ^ 4) := by decide +kernel
