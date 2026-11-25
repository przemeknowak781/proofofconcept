import Mathlib

/-!
# The tangent inequality for `log det`

For real matrices, `M` positive definite and `N` positive semidefinite,

    det N ≤ det M · exp (tr (M⁻¹ N) − n).

This is the concavity of `log det` at `M` in multiplicative form. Proof: `M = Rᴴ R` with `R` the
square root, the matrix `Q = R⁻ᴴ N R⁻¹` is positive semidefinite, `det Q = det N / det M`,
`tr Q = tr (M⁻¹ N)`, and `det Q ≤ exp (tr Q − n)` because `x ≤ exp (x − 1)` for each eigenvalue.
-/

open Matrix Finset

open scoped MatrixOrder

namespace Kenyon

variable {n : Type} [Fintype n] [DecidableEq n]

/-- `det Q ≤ exp (tr Q − n)` for a positive semidefinite real matrix. -/
theorem det_le_exp_trace {Q : Matrix n n ℝ} (hQ : Q.PosSemidef) :
    Q.det ≤ Real.exp (Q.trace - Fintype.card n) := by
  have hdet := hQ.isHermitian.det_eq_prod_eigenvalues
  have htr := hQ.isHermitian.trace_eq_sum_eigenvalues
  simp only [RCLike.ofReal_real_eq_id, id] at hdet htr
  rw [hdet, htr]
  calc ∏ i, hQ.isHermitian.eigenvalues i
      ≤ ∏ i, Real.exp (hQ.isHermitian.eigenvalues i - 1) :=
        Finset.prod_le_prod₀ (fun i _ => hQ.eigenvalues_nonneg i) (fun i _ => by
          have := Real.add_one_le_exp (hQ.isHermitian.eigenvalues i - 1)
          linarith)
    _ = Real.exp (∑ i, hQ.isHermitian.eigenvalues i - Fintype.card n) := by
        rw [← Real.exp_sum, Finset.sum_sub_distrib]
        simp

theorem det_le_of_factor (B : Matrix n n ℝ) (hB : B.det ≠ 0) {N : Matrix n n ℝ}
    (hN : N.PosSemidef) :
    N.det ≤ (Bᴴ * B).det * Real.exp (((Bᴴ * B)⁻¹ * N).trace - Fintype.card n) := by
  have hQ : ((B⁻¹)ᴴ * N * B⁻¹).PosSemidef := hN.conjTranspose_mul_mul_same B⁻¹
  have h := det_le_exp_trace hQ
  have hdetQ : ((B⁻¹)ᴴ * N * B⁻¹).det = N.det / (B.det ^ 2) := by
    rw [det_mul, det_mul, det_conjTranspose, det_nonsing_inv]
    simp only [star_trivial, Ring.inverse_eq_inv']
    field_simp
  have htrQ : ((B⁻¹)ᴴ * N * B⁻¹).trace = ((Bᴴ * B)⁻¹ * N).trace := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_inv_rev, conjTranspose_nonsing_inv]
  have hdetM : (Bᴴ * B).det = B.det ^ 2 := by
    rw [det_mul, det_conjTranspose]
    simp only [star_trivial]
    ring
  rw [hdetQ, htrQ] at h
  rw [hdetM]
  have hpos : 0 < B.det ^ 2 := by positivity
  rw [div_le_iff₀ hpos] at h
  linarith

/-- **Tangent inequality for `log det`.** -/
theorem det_le_det_mul_exp {M N : Matrix n n ℝ} (hM : M.PosDef) (hN : N.PosSemidef) :
    N.det ≤ M.det * Real.exp ((M⁻¹ * N).trace - Fintype.card n) := by
  have h0 : (0 : Matrix n n ℝ) ≤ M := hM.posSemidef.nonneg
  have hR : (CFC.sqrt M).PosSemidef := (CFC.sqrt_nonneg M).posSemidef
  have hRR : (CFC.sqrt M)ᴴ * CFC.sqrt M = M := by
    rw [hR.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self M h0
  have hdet : (CFC.sqrt M).det ≠ 0 := by
    intro h
    have hp := hM.det_pos
    rw [← hRR, det_mul, h] at hp
    simp at hp
  have := det_le_of_factor (CFC.sqrt M) hdet hN
  rwa [hRR] at this

end Kenyon
