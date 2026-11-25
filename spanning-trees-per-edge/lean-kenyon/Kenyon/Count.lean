import Kenyon.Bethe
import Kenyon.MatrixTree

/-!
# The bound with a polynomial factor

For a multigraph in which every degree is at least `2` and no edge joins two vertices of
degree `2`,

    numTrees ≤ |V|² · e³ · exp (|E| · (1/2) · log (27/8)).

Proof: `z = 1 − 1/|V|` in `det_Kmat_ge` (determinant to trees) and `det_Kmat_le_exp_Xi` (Bethe
bound), then `Xi z ≤ Xi 1 + 3` and the edge inequality `Xi 1 ≤ |E| · (1/2) · log (27/8)`.

`le_one_of_pow_le` is the elementary fact used later to remove the polynomial factor.
-/

open Finset

namespace Kenyon

open TreeEntropy

/-- If `ρ ^ N ≤ C · N²` for every `N ≥ 1`, then `ρ ≤ 1`. -/
theorem le_one_of_pow_le {ρ C : ℝ} (h : ∀ N : ℕ, 0 < N → ρ ^ N ≤ C * (N:ℝ) ^ 2) : ρ ≤ 1 := by
  by_contra hlt
  have h1 : 1 < ρ := not_le.1 hlt
  have hC : 0 < C := by
    have := h 1 one_pos
    simp at this
    linarith
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 2 h1
  have hev := (ht.eventually (gt_mem_nhds (show (0:ℝ) < 1 / C by positivity))).and
    (Filter.eventually_gt_atTop 0)
  obtain ⟨N, hN, hN0⟩ := hev.exists
  have hpow : 0 < ρ ^ N := by positivity
  rw [div_lt_iff₀ hpow] at hN
  have h2 := h N hN0
  have h3 : C * (N:ℝ) ^ 2 < ρ ^ N := by
    calc C * (N:ℝ) ^ 2 < C * (1 / C * ρ ^ N) := mul_lt_mul_of_pos_left hN hC
      _ = ρ ^ N := by field_simp
  linarith

variable {V E : Type} [Fintype E] [Fintype V] [DecidableEq V]

variable {src tgt : E → V} (hdeg : ∀ v, 2 ≤ deg src tgt v)
  (hD : ∀ e, ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2))

include hdeg hD in
/-- The edge inequality in terms of `Xi`. -/
theorem Xi_one_le_edges :
    Xi src tgt 1 ≤ (Fintype.card E : ℝ) * (1 / 2 * Real.log (27 / 8)) := by
  have h := xi_one_le hdeg hD
  unfold Xi Bfun Pof
  simpa using h

include hdeg hD in
/-- **The bound with a polynomial factor.** -/
theorem numTrees_le_classC (r : V) :
    (numTrees src tgt : ℝ) ≤ (Fintype.card V : ℝ) ^ 2
      * (Real.exp 3 * Real.exp ((Fintype.card E : ℝ) * (1 / 2 * Real.log (27 / 8)))) := by
  have hcard : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨r⟩
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hn1 : (1:ℝ) ≤ n := by
    rw [hn]
    exact_mod_cast hcard
  have hn0 : (0:ℝ) < n := by linarith
  set z : ℝ := 1 - 1 / n with hz
  have hinv : 1 / n ≤ 1 := by
    rw [div_le_one hn0]
    exact hn1
  have hz0 : 0 ≤ z := by
    rw [hz]
    linarith
  have hz1 : z < 1 := by
    have : 0 < 1 / n := by positivity
    rw [hz]
    linarith
  have A := det_Kmat_ge src tgt hz0 hz1.le r
  have B := det_Kmat_le_exp_Xi hdeg hD hz0 hz1
  have C := Xi_le_one hdeg hD hz0 hz1.le
  have D := Xi_one_le_edges hdeg hD
  have h1z : 1 - z = 1 / n := by
    rw [hz]
    ring
  have hC3 : (3:ℝ) * Fintype.card V * (1 - z) = 3 := by
    rw [h1z, ← hn]
    field_simp
  have hbern : 1 / n ≤ z ^ (Fintype.card V - 1) := by
    have h := one_add_mul_le_pow (show (-2:ℝ) ≤ -(1 / n) by linarith) (Fintype.card V - 1)
    have hcast : ((Fintype.card V - 1 : ℕ) : ℝ) = n - 1 := by
      rw [Nat.cast_sub hcard, hn]
      simp
    rw [hcast] at h
    have e1 : 1 + (n - 1) * -(1 / n) = 1 / n := by
      field_simp
      ring
    have e2 : (1 + -(1 / n)) = z := by
      rw [hz]
      ring
    rwa [e1, e2] at h
  have hd : (2:ℝ) ≤ deg src tgt r := by exact_mod_cast hdeg r
  have hτ : (0:ℝ) ≤ numTrees src tgt := Nat.cast_nonneg _
  set X : ℝ := Real.exp 3 * Real.exp ((Fintype.card E : ℝ) * (1 / 2 * Real.log (27 / 8)))
    with hX
  have hexp : Real.exp (Xi src tgt z) ≤ X := by
    rw [hX, ← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith
  rw [h1z] at A
  have key : 1 / n * 2 * (1 / n * (numTrees src tgt : ℝ)) ≤ X := by
    calc 1 / n * 2 * (1 / n * (numTrees src tgt : ℝ))
        ≤ 1 / n * (deg src tgt r : ℝ)
          * (z ^ (Fintype.card V - 1) * (numTrees src tgt : ℝ)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hd (by positivity))
            (mul_le_mul_of_nonneg_right hbern hτ) (by positivity) (by positivity)
      _ ≤ (Kmat src tgt z).det := A
      _ ≤ Real.exp (Xi src tgt z) := B
      _ ≤ X := hexp
  have hX0 : 0 ≤ X := by positivity
  have e3 : (numTrees src tgt : ℝ) = n ^ 2 / 2 * (1 / n * 2 * (1 / n * (numTrees src tgt : ℝ))) := by
    field_simp
  rw [e3]
  calc n ^ 2 / 2 * (1 / n * 2 * (1 / n * (numTrees src tgt : ℝ)))
      ≤ n ^ 2 / 2 * X := mul_le_mul_of_nonneg_left key (by positivity)
    _ ≤ n ^ 2 * X := by nlinarith [mul_nonneg (sq_nonneg n) hX0]

end Kenyon
