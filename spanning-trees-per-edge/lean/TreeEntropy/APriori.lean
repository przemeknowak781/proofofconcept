/-
  The lemma on a priori bounds as a statement about sequences of dart functions, and the
  resulting form of the edge inequality whose hypotheses are only the first-step relations.

  `Bounded src tgt hp hm` : the two a priori bounds,
        h_{u→v} ≤ 3/4 if d_u = 2,      h_{u→v} ≤ 4/(d_u + 3) if d_u ≥ 3.
  `bounded_step`    : if level `t` is bounded and level `t+1` satisfies the truncated first-step
                      inequality  h'_{u→v} · (d_u − Σ_{darts into u other than v→u} h) ≤ 1,
                      then level `t+1` is bounded;
  `bounded_iterate` : hence every level is bounded;
  `bounded_of_tendsto` : and so is a pointwise limit.
  `tree_entropy_bound_of_first_step` : the edge inequality for a positive solution `h` of the
                      first-step equation that is the limit of such a sequence.
-/
import TreeEntropy.Darts

open Finset Filter Topology

namespace TreeEntropy

variable {V E : Type} [Fintype E] [DecidableEq V]

/-- The a priori bounds. -/
def Bounded (src tgt : E → V) (hp hm : E → ℝ) : Prop :=
  (∀ e, deg src tgt (src e) = 2 → hp e ≤ 3 / 4) ∧
  (∀ e, deg src tgt (tgt e) = 2 → hm e ≤ 3 / 4) ∧
  (∀ e, 3 ≤ deg src tgt (src e) → hp e ≤ 4 / ((deg src tgt (src e) : ℝ) + 3)) ∧
  (∀ e, 3 ≤ deg src tgt (tgt e) → hm e ≤ 4 / ((deg src tgt (tgt e) : ℝ) + 3))

theorem bounded_zero (src tgt : E → V) : Bounded src tgt (fun _ => 0) (fun _ => 0) :=
  ⟨fun _ _ => by norm_num, fun _ _ => by norm_num, fun _ _ => by positivity,
    fun _ _ => by positivity⟩

theorem four_div_le {d : ℕ} (h3 : 3 ≤ d) : 4 / ((d:ℝ) + 3) ≤ 2 / 3 := by
  have hd : (3:ℝ) ≤ d := by exact_mod_cast h3
  rw [div_le_iff₀ (by positivity)]
  linarith

namespace Bounded

variable {src tgt : E → V} {hp hm : E → ℝ} (B : Bounded src tgt hp hm)
include B

theorem hp_le_two_thirds (e : E) (h3 : 3 ≤ deg src tgt (src e)) : hp e ≤ 2 / 3 :=
  (B.2.2.1 e h3).trans (four_div_le h3)

theorem hm_le_two_thirds (e : E) (h3 : 3 ≤ deg src tgt (tgt e)) : hm e ≤ 2 / 3 :=
  (B.2.2.2 e h3).trans (four_div_le h3)

theorem hp_le (hdeg : ∀ v, 2 ≤ deg src tgt v) (e : E) : hp e ≤ 3 / 4 := by
  rcases Nat.eq_or_lt_of_le (hdeg (src e)) with h2 | h3
  · exact B.1 e h2.symm
  · have := B.hp_le_two_thirds e h3
    linarith

theorem hm_le (hdeg : ∀ v, 2 ≤ deg src tgt v) (e : E) : hm e ≤ 3 / 4 := by
  rcases Nat.eq_or_lt_of_le (hdeg (tgt e)) with h2 | h3
  · exact B.2.1 e h2.symm
  · have := B.hm_le_two_thirds e h3
    linarith

end Bounded

omit [Fintype E] in
/-- A sum without one of its terms. -/
theorem sum_sub_le (s : Finset E) (f : E → ℝ) (c : ℝ) (e₀ : E) (he₀ : e₀ ∈ s)
    (h : ∀ e ∈ s, e ≠ e₀ → f e ≤ c) : ∑ e ∈ s, f e - f e₀ ≤ c * ((s.card : ℝ) - 1) := by
  classical
  rw [← Finset.add_sum_erase s f he₀]
  have h1 := sum_le_card_mul (s.erase e₀) f c
    fun e he => h e (Finset.mem_of_mem_erase he) (Finset.ne_of_mem_erase he)
  have hcard : ((s.erase e₀).card : ℝ) + 1 = s.card := by
    exact_mod_cast Finset.card_erase_add_one he₀
  rw [← hcard]
  linarith

/-- The darts into `src e` other than the reverse of the dart `src e → tgt e`. -/
theorem inSum_sub_hm_le (src tgt : E → V) (hp hm : E → ℝ) (e : E) (c : ℝ)
    (h1 : ∀ e', tgt e' = src e → hp e' ≤ c) (h2 : ∀ e', src e' = src e → e' ≠ e → hm e' ≤ c) :
    inSum src tgt hp hm (src e) - hm e ≤ c * ((deg src tgt (src e) : ℝ) - 1) := by
  have a1 := sum_le_card_mul (univ.filter fun e' => tgt e' = src e) hp c
    fun e' he' => h1 e' (Finset.mem_filter.1 he').2
  have a2 := sum_sub_le (univ.filter fun e' => src e' = src e) hm c e
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
    fun e' he' hne => h2 e' (Finset.mem_filter.1 he').2 hne
  unfold inSum deg
  push_cast
  linarith

/-- The darts into `tgt e` other than the reverse of the dart `tgt e → src e`. -/
theorem inSum_sub_hp_le (src tgt : E → V) (hp hm : E → ℝ) (e : E) (c : ℝ)
    (h1 : ∀ e', tgt e' = tgt e → e' ≠ e → hp e' ≤ c) (h2 : ∀ e', src e' = tgt e → hm e' ≤ c) :
    inSum src tgt hp hm (tgt e) - hp e ≤ c * ((deg src tgt (tgt e) : ℝ) - 1) := by
  have a1 := sum_sub_le (univ.filter fun e' => tgt e' = tgt e) hp c e
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
    fun e' he' hne => h1 e' (Finset.mem_filter.1 he').2 hne
  have a2 := sum_le_card_mul (univ.filter fun e' => src e' = tgt e) hm c
    fun e' he' => h2 e' (Finset.mem_filter.1 he').2
  unfold inSum deg
  push_cast
  linarith

/-- **A priori bounds, induction step.** -/
theorem bounded_step {src tgt : E → V} (hdeg : ∀ v, 2 ≤ deg src tgt v)
    (hD : ∀ e, ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2))
    {hp hm hp' hm' : E → ℝ} (B : Bounded src tgt hp hm)
    (step_p : ∀ e, hp' e
      * ((deg src tgt (src e) : ℝ) - (inSum src tgt hp hm (src e) - hm e)) ≤ 1)
    (step_m : ∀ e, hm' e
      * ((deg src tgt (tgt e) : ℝ) - (inSum src tgt hp hm (tgt e) - hp e)) ≤ 1) :
    Bounded src tgt hp' hm' := by
  refine ⟨fun e h2 => ?_, fun e h2 => ?_, fun e h3 => ?_, fun e h3 => ?_⟩
  · -- the tail `src e` has degree 2: the other dart into it comes from a vertex of degree ≥ 3
    have hS : inSum src tgt hp hm (src e) - hm e
        ≤ 2 / 3 * ((deg src tgt (src e) : ℝ) - 1) := by
      refine inSum_sub_hm_le src tgt hp hm e (2 / 3) (fun e' he' => ?_) (fun e' he' _ => ?_)
      · have h22 := hD e'
        have hge := hdeg (src e')
        have ht : deg src tgt (tgt e') = 2 := by rw [he']; exact h2
        exact B.hp_le_two_thirds e' (by omega)
      · have h22 := hD e'
        have hge := hdeg (tgt e')
        have hs : deg src tgt (src e') = 2 := by rw [he']; exact h2
        exact B.hm_le_two_thirds e' (by omega)
    have hd : (deg src tgt (src e) : ℝ) = 2 := by exact_mod_cast h2
    have hst := step_p e
    rw [hd] at hS hst
    rcases le_or_gt (hp' e) 0 with h0 | h0
    · linarith
    · have := mul_le_mul_of_nonneg_left
        (show (4:ℝ) / 3 ≤ 2 - (inSum src tgt hp hm (src e) - hm e) by linarith) h0.le
      linarith
  · have hS : inSum src tgt hp hm (tgt e) - hp e
        ≤ 2 / 3 * ((deg src tgt (tgt e) : ℝ) - 1) := by
      refine inSum_sub_hp_le src tgt hp hm e (2 / 3) (fun e' he' _ => ?_) (fun e' he' => ?_)
      · have h22 := hD e'
        have hge := hdeg (src e')
        have ht : deg src tgt (tgt e') = 2 := by rw [he']; exact h2
        exact B.hp_le_two_thirds e' (by omega)
      · have h22 := hD e'
        have hge := hdeg (tgt e')
        have hs : deg src tgt (src e') = 2 := by rw [he']; exact h2
        exact B.hm_le_two_thirds e' (by omega)
    have hd : (deg src tgt (tgt e) : ℝ) = 2 := by exact_mod_cast h2
    have hst := step_m e
    rw [hd] at hS hst
    rcases le_or_gt (hm' e) 0 with h0 | h0
    · linarith
    · have := mul_le_mul_of_nonneg_left
        (show (4:ℝ) / 3 ≤ 2 - (inSum src tgt hp hm (tgt e) - hp e) by linarith) h0.le
      linarith
  · -- the tail `src e` has degree d ≥ 3: every dart into it is at most 3/4
    have hS : inSum src tgt hp hm (src e) - hm e
        ≤ 3 / 4 * ((deg src tgt (src e) : ℝ) - 1) :=
      inSum_sub_hm_le src tgt hp hm e (3 / 4) (fun e' _ => B.hp_le hdeg e')
        (fun e' _ _ => B.hm_le hdeg e')
    have hd : (3:ℝ) ≤ deg src tgt (src e) := by exact_mod_cast h3
    have hst := step_p e
    rw [le_div_iff₀ (by positivity)]
    rcases le_or_gt (hp' e) 0 with h0 | h0
    · nlinarith [mul_nonneg (neg_nonneg.2 h0) (by linarith : (0:ℝ) ≤ deg src tgt (src e) + 3)]
    · have := mul_le_mul_of_nonneg_left
        (show ((deg src tgt (src e) : ℝ) + 3) / 4
          ≤ (deg src tgt (src e) : ℝ) - (inSum src tgt hp hm (src e) - hm e) by linarith) h0.le
      linarith
  · have hS : inSum src tgt hp hm (tgt e) - hp e
        ≤ 3 / 4 * ((deg src tgt (tgt e) : ℝ) - 1) :=
      inSum_sub_hp_le src tgt hp hm e (3 / 4) (fun e' _ _ => B.hp_le hdeg e')
        (fun e' _ => B.hm_le hdeg e')
    have hd : (3:ℝ) ≤ deg src tgt (tgt e) := by exact_mod_cast h3
    have hst := step_m e
    rw [le_div_iff₀ (by positivity)]
    rcases le_or_gt (hm' e) 0 with h0 | h0
    · nlinarith [mul_nonneg (neg_nonneg.2 h0) (by linarith : (0:ℝ) ≤ deg src tgt (tgt e) + 3)]
    · have := mul_le_mul_of_nonneg_left
        (show ((deg src tgt (tgt e) : ℝ) + 3) / 4
          ≤ (deg src tgt (tgt e) : ℝ) - (inSum src tgt hp hm (tgt e) - hp e) by linarith) h0.le
      linarith

/-- **A priori bounds for every level.** -/
theorem bounded_iterate {src tgt : E → V} (hdeg : ∀ v, 2 ≤ deg src tgt v)
    (hD : ∀ e, ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2))
    (Hp Hm : ℕ → E → ℝ) (base : Bounded src tgt (Hp 0) (Hm 0))
    (step_p : ∀ t e, Hp (t + 1) e
      * ((deg src tgt (src e) : ℝ) - (inSum src tgt (Hp t) (Hm t) (src e) - Hm t e)) ≤ 1)
    (step_m : ∀ t e, Hm (t + 1) e
      * ((deg src tgt (tgt e) : ℝ) - (inSum src tgt (Hp t) (Hm t) (tgt e) - Hp t e)) ≤ 1) :
    ∀ t, Bounded src tgt (Hp t) (Hm t) := by
  intro t
  induction t with
  | zero => exact base
  | succ t ih => exact bounded_step hdeg hD ih (step_p t) (step_m t)

/-- **A priori bounds for the limit.** -/
theorem bounded_of_tendsto {src tgt : E → V} {Hp Hm : ℕ → E → ℝ} {hp hm : E → ℝ}
    (hB : ∀ t, Bounded src tgt (Hp t) (Hm t))
    (limp : ∀ e, Tendsto (fun t => Hp t e) atTop (𝓝 (hp e)))
    (limm : ∀ e, Tendsto (fun t => Hm t e) atTop (𝓝 (hm e))) : Bounded src tgt hp hm :=
  ⟨fun e h => le_of_tendsto' (limp e) fun t => (hB t).1 e h,
    fun e h => le_of_tendsto' (limm e) fun t => (hB t).2.1 e h,
    fun e h => le_of_tendsto' (limp e) fun t => (hB t).2.2.1 e h,
    fun e h => le_of_tendsto' (limm e) fun t => (hB t).2.2.2 e h⟩

/-- **The universal-cover algebra and the edge inequality together.**  `hp, hm` is a positive
solution of the first-step equation; it is the pointwise limit of a sequence `Hp t, Hm t` whose
level 0 satisfies the a priori bounds (for instance is identically 0, see `bounded_zero`) and whose consecutive levels
satisfy the truncated first-step inequality.  Then

    ∑ v, log (d_v − inSum v) − ∑ e, log (1 − hp e · hm e) ≤ |E| · (1/2) log (27/8). -/
theorem tree_entropy_bound_of_first_step [Fintype V] (src tgt : E → V) (hp hm : E → ℝ)
    (Hp Hm : ℕ → E → ℝ)
    (hdeg : ∀ v, 2 ≤ deg src tgt v)
    (hD : ∀ e, ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2))
    (pos_p : ∀ e, 0 < hp e) (pos_m : ∀ e, 0 < hm e)
    (eq_p : ∀ e, hp e
      * ((deg src tgt (src e) : ℝ) - inSum src tgt hp hm (src e) + hm e) = 1)
    (eq_m : ∀ e, hm e
      * ((deg src tgt (tgt e) : ℝ) - inSum src tgt hp hm (tgt e) + hp e) = 1)
    (base : Bounded src tgt (Hp 0) (Hm 0))
    (step_p : ∀ t e, Hp (t + 1) e
      * ((deg src tgt (src e) : ℝ) - (inSum src tgt (Hp t) (Hm t) (src e) - Hm t e)) ≤ 1)
    (step_m : ∀ t e, Hm (t + 1) e
      * ((deg src tgt (tgt e) : ℝ) - (inSum src tgt (Hp t) (Hm t) (tgt e) - Hp t e)) ≤ 1)
    (limp : ∀ e, Tendsto (fun t => Hp t e) atTop (𝓝 (hp e)))
    (limm : ∀ e, Tendsto (fun t => Hm t e) atTop (𝓝 (hm e))) :
    ∑ v, Real.log ((deg src tgt v : ℝ) - inSum src tgt hp hm v)
        - ∑ e, Real.log (1 - hp e * hm e)
      ≤ (Fintype.card E : ℝ) * (1 / 2 * Real.log (27 / 8)) := by
  have B := bounded_of_tendsto (bounded_iterate hdeg hD Hp Hm base step_p step_m) limp limm
  exact tree_entropy_bound_of_darts'
    ⟨pos_p, pos_m, eq_p, eq_m, hdeg, hD, B.1, B.2.1, B.2.2.1, B.2.2.2⟩

end TreeEntropy
