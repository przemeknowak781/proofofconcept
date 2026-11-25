import Kenyon

/-! Axiom reports for the theorems of the package. Every report must list only
`propext`, `Classical.choice`, `Quot.sound` (or a subset). -/

-- the final statements
#print axioms Kenyon.kenyon_bound
#print axioms Kenyon.kenyon_sharp
#print axioms Kenyon.kenyon_bound_real
#print axioms Kenyon.numTrees_sq_le
#print axioms Kenyon.numTrees_le_pow
-- the chain
#print axioms Kenyon.xi_one_le
#print axioms Kenyon.green_sol
#print axioms Kenyon.Bfun_mono
#print axioms Kenyon.Xi_step
#print axioms Kenyon.det_le_det_mul_exp
#print axioms Kenyon.det_Kmat_step
#print axioms Kenyon.det_Kmat_le_exp_Xi
#print axioms Kenyon.numForests_le_det
#print axioms Kenyon.det_Kmat_ge
#print axioms Kenyon.numTrees_le_classC
#print axioms Kenyon.numTrees_pow_le
#print axioms Kenyon.numTrees_le_exp_classC
#print axioms Kenyon.numTreesWith_le_contract
#print axioms Kenyon.numTreesWithout_le_delete
#print axioms Kenyon.pendant_step
-- the sharpness chain
#print axioms Kenyon.card_le_of_conn
#print axioms Kenyon.exists_tree_of_forest
#print axioms Kenyon.numForests_le_numTrees_mul
#print axioms Kenyon.det_le_numForests
#print axioms Kenyon.det_redMat_expand
#print axioms Kenyon.det_Kmat_le_numTrees
#print axioms Kenyon.Xi_step_reg
#print axioms Kenyon.Xi_one_reg
#print axioms Kenyon.Act.green_upper
#print axioms Kenyon.Act.trace_inv_mul_Amat_le
#print axioms Kenyon.Act.uW_eq_zero_of_free
#print axioms Kenyon.sanov
#print axioms Kenyon.cay_free
#print axioms Kenyon.cay_conn
#print axioms Kenyon.det_Kmat_step_rev
#print axioms Kenyon.Act.logdet_ge
#print axioms Kenyon.Act.numTrees_ge
-- examples
#print axioms Kenyon.numTrees_digon
#print axioms Kenyon.numTrees_loop
