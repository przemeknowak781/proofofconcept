import Kenyon.Sanov
import Kenyon.MatrixTree2
import Kenyon.Bethe

/-!
# Sharpness of the bound

`kenyon_sharp`: for every real `0 < c < 27/8` there is a finite multigraph with `m ≥ 1` edges
and more than `c^(m/2)` spanning trees (`c^m < τ²`). So the constant `27/8` in `kenyon_bound`
cannot be replaced by a smaller one.

The graphs are the 4-regular graphs `cayAct n` of `Kenyon/Sanov.lean`. For a graph of an action
without closed reduced words of length `1, …, k+1`:

* `det_Kmat_step_rev` : `det K(a) ≤ det K(b) · exp ((b − a) · tr (K(b)⁻¹ A))`;
* `Act.logdet_ge`     : `Xi z − |V| · 2 z^(k+1)/(1 − z) ≤ log det K(z)` (telescoping, with the
  upper bound for the trace and the scalar step for `Xi`);
* `Act.numTrees_ge`   : with `z = 1 − y²/4`,
  `exp (|V| · (log (27/8) − 2 z^(k+1)/(1 − z) − 3 log (1 + y))) ≤ numTrees`.
-/

open Finset Matrix

namespace Kenyon

open TreeEntropy

section General

variable {V E : Type} [Fintype E] [Fintype V] [DecidableEq V]

/-- **The reverse one-step inequality for the determinant.** -/
theorem det_Kmat_step_rev {src tgt : E → V} (hdeg1 : ∀ v, 1 ≤ deg src tgt v) {a b : ℝ}
    (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b < 1) :
    (Kmat src tgt a).det ≤ (Kmat src tgt b).det
      * Real.exp ((b - a) * ((Kmat src tgt b)⁻¹ * Amat src tgt).trace) := by
  have hM := Kmat_posDef hdeg1 (ha0.trans hab) hb1
  have hN := (Kmat_posDef hdeg1 ha0 (hab.trans_lt hb1)).posSemidef
  have h := det_le_det_mul_exp hM hN
  have hunit : IsUnit (Kmat src tgt b).det := hM.det_pos.ne'.isUnit
  have htr : ((Kmat src tgt b)⁻¹ * Kmat src tgt a).trace - Fintype.card V
      = (b - a) * ((Kmat src tgt b)⁻¹ * Amat src tgt).trace := by
    rw [Kmat_eq_sub src tgt b a, Matrix.mul_sub, nonsing_inv_mul _ hunit, trace_sub,
      Matrix.mul_smul, trace_smul, trace_one, smul_eq_mul]
    ring
  rwa [htr] at h

end General

namespace Act

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (A : Act V)

theorem logdet_step_rev {k : ℕ} (hgirth : ∀ v j, 1 ≤ j → j ≤ k + 1 → A.uW v j v = 0)
    {a b z : ℝ} (ha0 : 0 ≤ a) (hab : a < b) (hbz : b ≤ z) (hz1 : z < 1) :
    -((b - a) * (Wsum esrc A.etgt b - Wsum esrc A.etgt a))
        - (b - a) * ((Fintype.card V : ℝ) * (2 * z ^ (k + 1) / (1 - z)))
      ≤ (Real.log (Kmat esrc A.etgt b).det - Xi esrc A.etgt b)
        - (Real.log (Kmat esrc A.etgt a).det - Xi esrc A.etgt a) := by
  have hreg : ∀ x, deg esrc A.etgt x = 4 := A.deg_act
  have hdeg1 : ∀ x, 1 ≤ deg esrc A.etgt x := fun x => by rw [hreg]; norm_num
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have hb0 : 0 < b := lt_of_le_of_lt ha0 hab
  have hb1 : b < 1 := lt_of_le_of_lt hbz hz1
  have pa := (Kmat_posDef hdeg1 ha0 (hab.trans hb1)).det_pos
  have pb := (Kmat_posDef hdeg1 hb0.le hb1).det_pos
  have h1 := Real.log_le_log pa (det_Kmat_step_rev hdeg1 ha0 hab.le hb1)
  rw [Real.log_mul pb.ne' (Real.exp_pos _).ne', Real.log_exp] at h1
  have : Nonempty V := ⟨v₀⟩
  have hT := A.trace_inv_mul_Amat_le hb0 hb1 k hgirth
  have hXi := Xi_step_reg hreg v₀ ha0 hab.le hb1.le
  have herr : 2 * b ^ (k + 1) / (1 - b) ≤ 2 * z ^ (k + 1) / (1 - z) := by
    have hpow : b ^ (k + 1) ≤ z ^ (k + 1) := pow_le_pow_left₀ hb0.le hbz _
    have hz0 : 0 ≤ z ^ (k + 1) := pow_nonneg (hb0.le.trans hbz) _
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right hpow (by linarith : (0:ℝ) ≤ 1 - z),
      mul_le_mul_of_nonneg_left (by linarith : 1 - z ≤ 1 - b) hz0]
  have hn : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hba : 0 < b - a := by linarith
  have hT' : ((Kmat esrc A.etgt b)⁻¹ * Amat esrc A.etgt).trace
      ≤ Wsum esrc A.etgt b + (Fintype.card V : ℝ) * (2 * z ^ (k + 1) / (1 - z)) := by
    have := mul_le_mul_of_nonneg_left herr hn
    linarith
  have h2 := mul_le_mul_of_nonneg_left hT' hba.le
  linarith

/-- **Lower bound for the determinant.** -/
theorem logdet_ge {k : ℕ} (hgirth : ∀ v j, 1 ≤ j → j ≤ k + 1 → A.uW v j v = 0)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Xi esrc A.etgt z - (Fintype.card V : ℝ) * (2 * z ^ (k + 1) / (1 - z))
      ≤ Real.log (Kmat esrc A.etgt z).det := by
  have hreg : ∀ x, deg esrc A.etgt x = 4 := A.deg_act
  have hdeg := two_le_deg_reg hreg
  have hD := no22_reg hreg
  set C : ℝ := (Fintype.card V : ℝ) * (2 * z ^ (k + 1) / (1 - z)) with hC
  have hC0 : 0 ≤ C := by
    have : 0 < 1 - z := by linarith
    positivity
  set F : ℝ → ℝ := fun t => Real.log (Kmat esrc A.etgt t).det - Xi esrc A.etgt t with hF
  have hF0 : F 0 = 0 := by
    simp only [hF]
    rw [Kmat_zero_det, Xi_zero hdeg hD, Real.log_prod]
    · ring
    · intro v _
      have : (2:ℝ) ≤ deg esrc A.etgt v := by exact_mod_cast hdeg v
      exact ne_of_gt (by linarith)
  rcases hz0.eq_or_lt with hz | hzpos
  · have h0 : F z = 0 := by rw [← hz]; exact hF0
    simp only [hF] at h0
    linarith
  have key : ∀ N : ℕ, 0 < N → -(z / N * (3 * Fintype.card V)) - z * C ≤ F z := by
    intro N hN
    have hNr : (0:ℝ) < N := by exact_mod_cast hN
    set t : ℕ → ℝ := fun j => z * j / N with ht
    have ht0 : t 0 = 0 := by simp [ht]
    have htN : t N = z := by
      simp only [ht]
      field_simp
    have hstep : ∀ j ∈ Finset.range N,
        -(z / N * (Wsum esrc A.etgt (t (j + 1)) - Wsum esrc A.etgt (t j))) - z / N * C
          ≤ F (t (j + 1)) - F (t j) := by
      intro j hj
      have hj' : ((j + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Finset.mem_range.1 hj
      have h0 : 0 ≤ t j := by
        simp only [ht]
        positivity
      have hd : t (j + 1) - t j = z / N := by
        simp only [ht]
        push_cast
        field_simp
        ring
      have h01 : t j < t (j + 1) := by
        have : 0 < z / N := by positivity
        linarith
      have h1 : t (j + 1) ≤ z := by
        simp only [ht]
        rw [div_le_iff₀ hNr]
        nlinarith
      have := A.logdet_step_rev hgirth h0 h01 h1 hz1
      rw [hd] at this
      exact this
    have hsum := Finset.sum_le_sum hstep
    have e1 : ∑ j ∈ Finset.range N, (F (t (j + 1)) - F (t j)) = F (t N) - F (t 0) :=
      Finset.sum_range_sub (fun j => F (t j)) N
    have e2 : ∑ j ∈ Finset.range N,
        (-(z / N * (Wsum esrc A.etgt (t (j + 1)) - Wsum esrc A.etgt (t j))) - z / N * C)
        = -(z / N * (Wsum esrc A.etgt (t N) - Wsum esrc A.etgt (t 0))) - z * C := by
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
        Finset.sum_range_sub (fun j => Wsum esrc A.etgt (t j)) N, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      field_simp
    rw [e1, e2, ht0, htN, hF0] at hsum
    have hW1 := Wsum_le hdeg hD hz0 hz1.le
    have hW0 := Wsum_nonneg hdeg hD (le_refl (0:ℝ)) zero_le_one
    have hzN : 0 ≤ z / N := by positivity
    have := mul_le_mul_of_nonneg_left
      (by linarith : Wsum esrc A.etgt z - Wsum esrc A.etgt 0 ≤ 3 * Fintype.card V) hzN
    linarith
  have hFz : -(z * C) ≤ F z := by
    by_contra h
    have hpos : 0 < -(z * C) - F z := by linarith [not_le.1 h]
    obtain ⟨N, hN⟩ := exists_nat_gt (z * (3 * Fintype.card V) / (-(z * C) - F z))
    have hNpos : (0:ℝ) < N := lt_of_le_of_lt (by positivity) hN
    have hN' : 0 < N := by exact_mod_cast hNpos
    have h1 := key N hN'
    rw [div_lt_iff₀ hpos] at hN
    have : z / N * (3 * Fintype.card V) < -(z * C) - F z := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hNpos]
      linarith
    linarith
  have hzC : z * C ≤ C := by nlinarith
  simp only [hF] at hFz
  linarith

/-- **Lower bound for the number of spanning trees.** -/
theorem numTrees_ge (hconn : ∀ x y, Conn esrc A.etgt univ x y) {k : ℕ}
    (hgirth : ∀ v j, 1 ≤ j → j ≤ k + 1 → A.uW v j v = 0) {y : ℝ} (hy0 : 0 < y)
    (hy1 : y ≤ 1) :
    Real.exp ((Fintype.card V : ℝ) * (Real.log (27 / 8)
        - 2 * (1 - y ^ 2 / 4) ^ (k + 1) / (y ^ 2 / 4) - 3 * Real.log (1 + y)))
      ≤ (numTrees esrc A.etgt : ℝ) := by
  have hreg : ∀ x, deg esrc A.etgt x = 4 := A.deg_act
  have hdeg := two_le_deg_reg hreg
  have hD := no22_reg hreg
  have hdeg1 : ∀ x, 1 ≤ deg esrc A.etgt x := fun x => by rw [hreg]; norm_num
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have : Nonempty V := ⟨v₀⟩
  set z : ℝ := 1 - y ^ 2 / 4 with hz
  have hy2 : y ^ 2 ≤ 1 := by nlinarith
  have hz0 : 0 ≤ z := by rw [hz]; linarith
  have hz1 : z < 1 := by
    rw [hz]
    have : 0 < y ^ 2 := by positivity
    linarith
  have h1z : 1 - z = y ^ 2 / 4 := by rw [hz]; ring
  set N : ℝ := (Fintype.card V : ℝ) with hN
  have L1 := A.logdet_ge hgirth hz0 hz1
  have L2 : Xi esrc A.etgt 1 ≤ Xi esrc A.etgt z := by
    have h := Xi_step_reg hreg v₀ hz0 hz1.le (le_refl (1:ℝ))
    have hW := Wsum_nonneg hdeg hD hz0 hz1.le
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - z) hW]
  have L3 := Xi_one_reg hreg v₀
  have hc : ∀ v, (1 - z) * (deg esrc A.etgt v : ℝ) ≤ y ^ 2 := by
    intro v
    rw [hreg, h1z]
    push_cast
    linarith
  have L4 := det_Kmat_le_numTrees esrc A.etgt hconn hz0 hz1.le hy0.le hy1 hc
  have hcardE : Fintype.card (V × Fin 2) = Fintype.card V * 2 := by
    rw [Fintype.card_prod, Fintype.card_fin]
  rw [hcardE] at L4
  have pz := (Kmat_posDef hdeg1 hz0 hz1).det_pos
  have hy1' : (0:ℝ) < 1 + y := by linarith
  have hpow : (1 + y) ^ (Fintype.card V + Fintype.card V * 2)
      = Real.exp (N * (3 * Real.log (1 + y))) := by
    have e : Fintype.card V + Fintype.card V * 2 = Fintype.card V * 3 := by ring
    rw [e, ← Real.exp_log (pow_pos hy1' (Fintype.card V * 3)), Real.log_pow]
    congr 1
    push_cast
    ring
  rw [hpow] at L4
  -- exp (log det) = det
  have L5 : Real.exp (N * Real.log (27 / 8) - N * (2 * z ^ (k + 1) / (1 - z)))
      ≤ (Kmat esrc A.etgt z).det := by
    rw [← Real.exp_log pz]
    apply Real.exp_le_exp.2
    rw [← L3]
    linarith
  have hsplit : Real.exp (N * Real.log (27 / 8) - N * (2 * z ^ (k + 1) / (1 - z)))
      = Real.exp (N * (Real.log (27 / 8) - 2 * z ^ (k + 1) / (y ^ 2 / 4) - 3 * Real.log (1 + y)))
        * Real.exp (N * (3 * Real.log (1 + y))) := by
    rw [← Real.exp_add, h1z]
    congr 1
    ring
  rw [hsplit] at L5
  have hpos : 0 < Real.exp (N * (3 * Real.log (1 + y))) := Real.exp_pos _
  exact le_of_mul_le_mul_right (L5.trans L4) hpos

end Act

/-- **Sharpness.** For every `0 < c < 27/8` there is a finite multigraph with `m ≥ 1` edges and
`c^m < τ²`, that is, with more than `c^(m/2)` spanning trees. -/
theorem kenyon_sharp (c : ℝ) (hc0 : 0 < c) (hc : c < 27 / 8) :
    ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (src tgt : E → V),
      0 < Fintype.card E ∧ c ^ Fintype.card E < (numTrees src tgt : ℝ) ^ 2 := by
  classical
  -- the margin
  set η : ℝ := Real.log (27 / 8) - Real.log c with hη
  have hη0 : 0 < η := by
    rw [hη]
    have := Real.log_lt_log hc0 hc
    linarith
  -- the parameter `y`
  set y : ℝ := min 1 (η / 7) with hy
  have hy0 : 0 < y := lt_min one_pos (by positivity)
  have hy1 : y ≤ 1 := min_le_left _ _
  have hyη : y ≤ η / 7 := min_le_right _ _
  have hlog : Real.log (1 + y) ≤ y := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + y)
    linarith
  set z : ℝ := 1 - y ^ 2 / 4 with hz
  have hy2 : y ^ 2 ≤ 1 := by nlinarith
  have hy2pos : 0 < y ^ 2 / 4 := by positivity
  have hz0 : 0 ≤ z := by rw [hz]; linarith
  have hz1 : z < 1 := by rw [hz]; linarith
  -- the parameter `k`
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < η * (y ^ 2 / 4) / 4) hz1
  have hk' : 2 * z ^ (k + 1) / (y ^ 2 / 4) < η / 2 := by
    have hzk : z ^ (k + 1) ≤ z ^ k := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (by positivity) hz1.le
    rw [div_lt_iff₀ hy2pos]
    linarith
  -- the graph
  set n : ℕ := 3 ^ (k + 1) + 2 with hn
  have : NeZero n := ⟨by rw [hn]; positivity⟩
  have hfree : ∀ (v : HS n) (j : ℕ), 1 ≤ j → j ≤ k + 1 → (cayAct n).uW v j v = 0 := fun v =>
    (cayAct n).uW_eq_zero_of_free v (k + 1)
      (fun w hw hlen hr => cay_free n (k + 1) (by rw [hn]; omega) v w hw hlen hr)
  have : Nonempty (HS n) := ⟨1⟩
  have hlow := (cayAct n).numTrees_ge (cay_conn n) hfree hy0 hy1
  refine ⟨HS n, HS n × Fin 2, inferInstance, inferInstance, Act.esrc, (cayAct n).etgt, ?_, ?_⟩
  · rw [Fintype.card_prod, Fintype.card_fin]
    have : 0 < Fintype.card (HS n) := Fintype.card_pos
    omega
  · set N : ℕ := Fintype.card (HS n) with hN
    have hNpos : (0:ℝ) < N := by
      have : 0 < Fintype.card (HS n) := Fintype.card_pos
      exact_mod_cast this
    -- the exponent exceeds `N · log c`
    have hbr : Real.log c < Real.log (27 / 8)
        - 2 * (1 - y ^ 2 / 4) ^ (k + 1) / (y ^ 2 / 4) - 3 * Real.log (1 + y) := by
      rw [← hz]
      linarith
    have hcN : c ^ N < (numTrees Act.esrc (cayAct n).etgt : ℝ) := by
      have h1 : c ^ N = Real.exp ((N:ℝ) * Real.log c) := by
        rw [Real.exp_natCast_mul, Real.exp_log hc0]
      rw [h1]
      refine lt_of_lt_of_le (Real.exp_lt_exp.2 ?_) hlow
      exact mul_lt_mul_of_pos_left hbr hNpos
    have hcard : Fintype.card (HS n × Fin 2) = N * 2 := by
      rw [Fintype.card_prod, Fintype.card_fin]
    rw [hcard, pow_mul]
    exact pow_lt_pow_left₀ hcN (by positivity) (by norm_num)

end Kenyon
