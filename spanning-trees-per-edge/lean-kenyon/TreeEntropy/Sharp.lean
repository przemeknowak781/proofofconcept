/-
  Consistency and sharpness of the hypotheses of `tree_entropy_bound`.

  Two vertices joined by four parallel edges, `x = 3/8` at both vertices, `r = 1/8` on every
  edge.  Every hypothesis of `tree_entropy_bound` holds, and the conclusion holds with equality.
  So the hypotheses are jointly satisfiable, and the constant `(1/2) log (27/8)` cannot be
  lowered in this statement.
-/
import TreeEntropy.APriori

open Finset

namespace TreeEntropy.Sharp

def src : Fin 4 → Fin 2 := fun _ => 0
def tgt : Fin 4 → Fin 2 := fun _ => 1
noncomputable def x : Fin 2 → ℝ := fun _ => 3 / 8
noncomputable def r : Fin 4 → ℝ := fun _ => 1 / 8

theorem deg_eq (v : Fin 2) : deg src tgt v = 4 := by
  revert v; decide

theorem endSum_eq (v : Fin 2) : endSum src tgt r v = 1 / 2 := by
  have h : endSum src tgt r v = (deg src tgt v : ℝ) * (1 / 8) := by
    simp only [endSum, deg, r, Finset.sum_const, nsmul_eq_mul]
    push_cast; ring
  rw [h, deg_eq]; norm_num

theorem hyps_and_equality :
    (∀ e, 0 < r e) ∧
    (∀ e, r e * (1 + r e) = x (src e) * x (tgt e)) ∧
    (∀ v, endSum src tgt r v = deg src tgt v * x v - 1) ∧
    (∀ v, 2 ≤ deg src tgt v) ∧
    (∀ e, ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2)) ∧
    (∀ v, deg src tgt v = 2 → x v - 1 / (deg src tgt v : ℝ) ≤ 1) ∧
    (∀ v, 3 ≤ deg src tgt v → x v - 1 / (deg src tgt v : ℝ) ≤ 3 / (deg src tgt v : ℝ)) ∧
    (∀ v, 3 ≤ deg src tgt v → x v - 1 / (deg src tgt v : ℝ) ≤ Rprime (deg src tgt v)) ∧
    ∑ e, Real.log (1 + r e) - ∑ v, Real.log (x v)
      = (Fintype.card (Fin 4) : ℝ) * (1 / 2 * Real.log (27 / 8)) := by
  refine ⟨fun e => by simp [r], fun e => by simp only [r, x]; norm_num, fun v => ?_,
    fun v => by rw [deg_eq]; norm_num, fun e => by rw [deg_eq]; norm_num,
    fun v h => by rw [deg_eq] at h; norm_num at h, fun v _ => ?_, fun v _ => ?_, ?_⟩
  · rw [endSum_eq, deg_eq]; simp only [x]; norm_num
  · rw [deg_eq]; simp only [x]; norm_num
  · rw [deg_eq]; simp only [x, Rprime]; norm_num
  · have h98 : Real.log (1 + 1 / 8) = 2 * Real.log 3 - 3 * Real.log 2 := by
      rw [show (1:ℝ) + 1 / 8 = 3 ^ 2 / 2 ^ 3 by norm_num,
        Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      push_cast; ring
    have h38 : Real.log (3 / 8) = Real.log 3 - 3 * Real.log 2 := by
      rw [show (3:ℝ) / 8 = 3 / 2 ^ 3 by norm_num,
        Real.log_div (by positivity) (by positivity), Real.log_pow]
      push_cast; ring
    have h278 : Real.log (27 / 8) = 3 * Real.log 3 - 3 * Real.log 2 := by
      rw [show (27:ℝ) / 8 = 3 ^ 3 / 2 ^ 3 by norm_num,
        Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      push_cast; ring
    simp only [r, x, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      h98, h38, h278]
    push_cast; ring

/-! ### The same example as a dart function: every dart has value `1/3` -/

theorem inSum_eq (v : Fin 2) :
    inSum src tgt (fun _ => (1:ℝ) / 3) (fun _ => (1:ℝ) / 3) v = 4 / 3 := by
  have h : inSum src tgt (fun _ => (1:ℝ) / 3) (fun _ => (1:ℝ) / 3) v
      = (deg src tgt v : ℝ) * (1 / 3) := by
    simp only [inSum, deg, Finset.sum_const, nsmul_eq_mul]
    push_cast; ring
  rw [h, deg_eq]; norm_num

/-- The hypotheses `Darts` are satisfiable: four parallel edges, every dart equal to `1/3`. -/
theorem darts : Darts src tgt (fun _ => (1:ℝ) / 3) (fun _ => (1:ℝ) / 3) where
  pos_p := fun _ => by norm_num
  pos_m := fun _ => by norm_num
  eq_p := fun e => by rw [inSum_eq, deg_eq]; norm_num
  eq_m := fun e => by rw [inSum_eq, deg_eq]; norm_num
  deg_ge := fun v => by rw [deg_eq]; norm_num
  no22 := fun e => by rw [deg_eq]; norm_num
  two_p := fun e h => by rw [deg_eq] at h; norm_num at h
  two_m := fun e h => by rw [deg_eq] at h; norm_num at h
  three_p := fun e _ => by rw [deg_eq]; norm_num
  three_m := fun e _ => by rw [deg_eq]; norm_num

/-- For this dart function `x = 3/8` and `r = 1/8`, the equality case above. -/
theorem darts_x (v : Fin 2) : xOf src tgt (fun _ => (1:ℝ) / 3) (fun _ => (1:ℝ) / 3) v = x v := by
  unfold xOf x; rw [inSum_eq, deg_eq]; norm_num

theorem darts_r (e : Fin 4) : rOf (fun _ => (1:ℝ) / 3) (fun _ => (1:ℝ) / 3) e = r e := by
  unfold rOf r; norm_num

/-- The hypotheses of `tree_entropy_bound_of_first_step` are jointly satisfiable: take the
constant sequence equal to this dart function at every level. -/
theorem first_step_instance :
    ∑ v, Real.log ((deg src tgt v : ℝ) - inSum src tgt (fun _ => (1:ℝ) / 3) (fun _ => (1:ℝ) / 3) v)
        - ∑ _e : Fin 4, Real.log (1 - (1:ℝ) / 3 * (1 / 3))
      ≤ (Fintype.card (Fin 4) : ℝ) * (1 / 2 * Real.log (27 / 8)) :=
  tree_entropy_bound_of_first_step src tgt (fun _ => (1:ℝ) / 3) (fun _ => (1:ℝ) / 3)
    (fun _ _ => (1:ℝ) / 3) (fun _ _ => (1:ℝ) / 3) darts.deg_ge darts.no22 darts.pos_p darts.pos_m
    darts.eq_p darts.eq_m ⟨darts.two_p, darts.two_m, darts.three_p, darts.three_m⟩
    (fun _ e => by
      show (1:ℝ) / 3 * ((deg src tgt (src e) : ℝ)
        - (inSum src tgt (fun _ => (1:ℝ) / 3) (fun _ => (1:ℝ) / 3) (src e) - 1 / 3)) ≤ 1
      rw [inSum_eq, deg_eq]; norm_num)
    (fun _ e => by
      show (1:ℝ) / 3 * ((deg src tgt (tgt e) : ℝ)
        - (inSum src tgt (fun _ => (1:ℝ) / 3) (fun _ => (1:ℝ) / 3) (tgt e) - 1 / 3)) ≤ 1
      rw [inSum_eq, deg_eq]; norm_num)
    (fun _ => tendsto_const_nhds) (fun _ => tendsto_const_nhds)

end TreeEntropy.Sharp
