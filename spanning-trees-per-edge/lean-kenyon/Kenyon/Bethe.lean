import Kenyon.Lap

/-!
# The Bethe bound for the determinant

For a multigraph in which every degree is at least `2` and no edge joins two vertices of
degree `2`, and for `0 ≤ z < 1`,

    det (D − zA) ≤ exp (Xi z),      Xi z = ∑ v, log P_v(z) − ∑ e, log (1 − q_e(z)).

Proof. Put `F t = log det K(t) − Xi t`. Then `F 0 = 0`, and for `0 ≤ a ≤ b < 1`

    F b − F a ≤ (b − a) · (Wsum b − Wsum a)

(`det_Kmat_step` and `Xi_step`). Summing over the uniform partition of `[0, z]` into `N` parts
gives `F z ≤ (z / N) · (Wsum z − Wsum 0) ≤ 3 |V| z / N` for every `N`, hence `F z ≤ 0`.
No derivative of the solution of the dart system is used.
-/

open Finset

namespace Kenyon

open TreeEntropy

variable {V E : Type} [Fintype E] [Fintype V] [DecidableEq V]

variable {src tgt : E → V} (hdeg : ∀ v, 2 ≤ deg src tgt v)
  (hD : ∀ e, ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2))

include hdeg hD in
theorem logdet_step {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b < 1) :
    (Real.log (Kmat src tgt b).det - Xi src tgt b)
        - (Real.log (Kmat src tgt a).det - Xi src tgt a)
      ≤ (b - a) * (Wsum src tgt b - Wsum src tgt a) := by
  have hdeg1 : ∀ v, 1 ≤ deg src tgt v := fun v => le_trans (by norm_num) (hdeg v)
  have pa := (Kmat_posDef hdeg1 ha0 (hab.trans_lt hb1)).det_pos
  have pb := (Kmat_posDef hdeg1 (ha0.trans hab) hb1).det_pos
  have h1 := Real.log_le_log pb (det_Kmat_step hdeg hD ha0 hab hb1)
  rw [Real.log_mul pa.ne' (Real.exp_pos _).ne', Real.log_exp] at h1
  have h2 := Xi_step hdeg hD ha0 hab hb1.le
  linarith

include hdeg hD in
/-- **The Bethe bound for the determinant.** -/
theorem det_Kmat_le_exp_Xi {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    (Kmat src tgt z).det ≤ Real.exp (Xi src tgt z) := by
  have hdeg1 : ∀ v, 1 ≤ deg src tgt v := fun v => le_trans (by norm_num) (hdeg v)
  set F : ℝ → ℝ := fun t => Real.log (Kmat src tgt t).det - Xi src tgt t with hF
  have hF0 : F 0 = 0 := by
    simp only [hF]
    rw [Kmat_zero_det, Xi_zero hdeg hD, Real.log_prod]
    · ring
    · intro v _
      have : (2:ℝ) ≤ deg src tgt v := by exact_mod_cast hdeg v
      exact ne_of_gt (by linarith)
  have key : ∀ N : ℕ, 0 < N → F z ≤ z / N * (3 * Fintype.card V) := by
    intro N hN
    have hNr : (0:ℝ) < N := by exact_mod_cast hN
    set t : ℕ → ℝ := fun k => z * k / N with ht
    have ht0 : t 0 = 0 := by simp [ht]
    have htN : t N = z := by
      simp only [ht]
      field_simp
    have hstep : ∀ k ∈ Finset.range N, F (t (k + 1)) - F (t k)
        ≤ z / N * (Wsum src tgt (t (k + 1)) - Wsum src tgt (t k)) := by
      intro k hk
      have hk' : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Finset.mem_range.1 hk
      have h0 : 0 ≤ t k := by
        simp only [ht]
        positivity
      have hd : t (k + 1) - t k = z / N := by
        simp only [ht]
        push_cast
        field_simp
        ring
      have h01 : t k ≤ t (k + 1) := by
        have : 0 ≤ z / N := by positivity
        linarith
      have h1 : t (k + 1) < 1 := by
        have : t (k + 1) ≤ z := by
          simp only [ht]
          rw [div_le_iff₀ hNr]
          nlinarith
        linarith
      have := logdet_step hdeg hD h0 h01 h1
      rw [hd] at this
      exact this
    have hsum := Finset.sum_le_sum hstep
    have e1 : ∑ k ∈ Finset.range N, (F (t (k + 1)) - F (t k)) = F (t N) - F (t 0) :=
      Finset.sum_range_sub (fun k => F (t k)) N
    have e2 : ∑ k ∈ Finset.range N, z / N * (Wsum src tgt (t (k + 1)) - Wsum src tgt (t k))
        = z / N * (Wsum src tgt (t N) - Wsum src tgt (t 0)) := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_range_sub (fun k => Wsum src tgt (t k)) N
    rw [e1, e2, ht0, htN, hF0] at hsum
    have hW1 := Wsum_le hdeg hD hz0 hz1.le
    have hW0 := Wsum_nonneg hdeg hD (le_refl (0:ℝ)) zero_le_one
    have hzN : 0 ≤ z / N := by positivity
    have := mul_le_mul_of_nonneg_left
      (by linarith : Wsum src tgt z - Wsum src tgt 0 ≤ 3 * Fintype.card V) hzN
    linarith
  have hFz : F z ≤ 0 := by
    by_contra h
    have hpos : 0 < F z := not_le.1 h
    obtain ⟨N, hN⟩ := exists_nat_gt (z * (3 * Fintype.card V) / F z)
    have hNpos : (0:ℝ) < N := lt_of_le_of_lt (by positivity) hN
    have hN' : 0 < N := by exact_mod_cast hNpos
    have h1 := key N hN'
    rw [div_lt_iff₀ hpos] at hN
    have : z / N * (3 * Fintype.card V) < F z := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hNpos]
      linarith
    linarith
  have pz := (Kmat_posDef hdeg1 hz0 hz1).det_pos
  rw [← Real.log_le_iff_le_exp pz]
  simp only [hF] at hFz
  linarith

end Kenyon
