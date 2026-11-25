/-
  From a dart function to the hypotheses of `tree_entropy_bound` (the section of the paper on
  the universal cover).

  Data: a finite multigraph `src tgt : E → V` and two reals per edge, `hp e` for the dart
  `src e → tgt e` and `hm e` for the dart `tgt e → src e`.  `inSum v` is the sum of the values of
  the darts pointing into `v`.

  `Darts src tgt hp hm` collects, as hypotheses:
    * positivity of the dart values;
    * the first-step equation:  h_{u→v} · (d_u − Σ_{darts into u other than v→u} h) = 1;
    * the degree condition (D);
    * the a priori bounds:  h_{u→v} ≤ 3/4 if d_u = 2,  h_{u→v} ≤ 4/(d_u + 3) if d_u ≥ 3.

  From these, with  x v = 1/(d_v − inSum v),  q e = hp e · hm e,  r e = q e/(1 − q e):
    * `Darts.I1`, `Darts.I2`       the identities (I1), (I2);
    * `Darts.R2`, `Darts.R3`, `Darts.R3'`   the three ranges (lemma on ranges, parts (a), (b), (c));
    * `tree_entropy_bound_of_darts`       the conclusion of the edge inequality;
    * `tree_entropy_bound_of_darts'`      the same, written directly in the dart values:
          ∑ v, log (d_v − inSum v) − ∑ e, log (1 − hp e · hm e) ≤ |E| · (1/2) log (27/8).
-/
import TreeEntropy.Main

open Finset

namespace TreeEntropy

variable {V E : Type} [Fintype E] [DecidableEq V]

/-- Sum of the values of the darts pointing into `v`. -/
def inSum (src tgt : E → V) (hp hm : E → ℝ) (v : V) : ℝ :=
  ∑ e ∈ univ.filter (fun e => tgt e = v), hp e + ∑ e ∈ univ.filter (fun e => src e = v), hm e

/-- `x v = 1/(d_v − inSum v)`. -/
noncomputable def xOf (src tgt : E → V) (hp hm : E → ℝ) (v : V) : ℝ :=
  1 / ((deg src tgt v : ℝ) - inSum src tgt hp hm v)

/-- `r e = q e/(1 − q e)` with `q e = hp e · hm e`. -/
noncomputable def rOf (hp hm : E → ℝ) (e : E) : ℝ := hp e * hm e / (1 - hp e * hm e)

omit [Fintype E] in
theorem sum_le_card_mul (s : Finset E) (f : E → ℝ) (c : ℝ) (h : ∀ e ∈ s, f e ≤ c) :
    ∑ e ∈ s, f e ≤ c * s.card := by
  have := Finset.sum_le_card_nsmul s f c h
  rw [nsmul_eq_mul] at this
  linarith

omit [Fintype E] in
/-- One summand is smaller by `δ`. -/
theorem sum_le_card_mul_sub (s : Finset E) (f : E → ℝ) (c δ : ℝ) (e₀ : E) (he₀ : e₀ ∈ s)
    (h : ∀ e ∈ s, f e ≤ c) (h0 : f e₀ ≤ c - δ) : ∑ e ∈ s, f e ≤ c * s.card - δ := by
  classical
  rw [← Finset.add_sum_erase s f he₀]
  have h1 := sum_le_card_mul (s.erase e₀) f c fun e he => h e (Finset.mem_of_mem_erase he)
  have hcard : ((s.erase e₀).card : ℝ) + 1 = s.card := by
    exact_mod_cast Finset.card_erase_add_one he₀
  rw [← hcard]
  linarith

theorem inSum_le (src tgt : E → V) (hp hm : E → ℝ) (v : V) (c : ℝ)
    (h1 : ∀ e, tgt e = v → hp e ≤ c) (h2 : ∀ e, src e = v → hm e ≤ c) :
    inSum src tgt hp hm v ≤ c * deg src tgt v := by
  have a1 := sum_le_card_mul (univ.filter fun e => tgt e = v) hp c
    fun e he => h1 e (Finset.mem_filter.1 he).2
  have a2 := sum_le_card_mul (univ.filter fun e => src e = v) hm c
    fun e he => h2 e (Finset.mem_filter.1 he).2
  unfold inSum deg
  push_cast
  linarith

/-- All incoming darts are at most `c`, and one of them is at most `c − δ`. -/
theorem inSum_le_special (src tgt : E → V) (hp hm : E → ℝ) (v : V) (c δ : ℝ)
    (h1 : ∀ e, tgt e = v → hp e ≤ c) (h2 : ∀ e, src e = v → hm e ≤ c)
    (hex : (∃ e, tgt e = v ∧ hp e ≤ c - δ) ∨ (∃ e, src e = v ∧ hm e ≤ c - δ)) :
    inSum src tgt hp hm v ≤ c * deg src tgt v - δ := by
  have a1 := sum_le_card_mul (univ.filter fun e => tgt e = v) hp c
    fun e he => h1 e (Finset.mem_filter.1 he).2
  have a2 := sum_le_card_mul (univ.filter fun e => src e = v) hm c
    fun e he => h2 e (Finset.mem_filter.1 he).2
  rcases hex with ⟨e₀, he, h0⟩ | ⟨e₀, he, h0⟩
  · have b1 := sum_le_card_mul_sub (univ.filter fun e => tgt e = v) hp c δ e₀
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩)
      (fun e he => h1 e (Finset.mem_filter.1 he).2) h0
    unfold inSum deg
    push_cast
    linarith
  · have b2 := sum_le_card_mul_sub (univ.filter fun e => src e = v) hm c δ e₀
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩)
      (fun e he => h2 e (Finset.mem_filter.1 he).2) h0
    unfold inSum deg
    push_cast
    linarith

/-- A positive dart function satisfying the first-step equations and the a priori bounds (the
lemma on a priori bounds of the paper), on a multigraph with all degrees `≥ 2` and no edge between two vertices of
degree 2. -/
structure Darts (src tgt : E → V) (hp hm : E → ℝ) : Prop where
  pos_p : ∀ e, 0 < hp e
  pos_m : ∀ e, 0 < hm e
  eq_p : ∀ e, hp e * ((deg src tgt (src e) : ℝ) - inSum src tgt hp hm (src e) + hm e) = 1
  eq_m : ∀ e, hm e * ((deg src tgt (tgt e) : ℝ) - inSum src tgt hp hm (tgt e) + hp e) = 1
  deg_ge : ∀ v, 2 ≤ deg src tgt v
  no22 : ∀ e, ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2)
  two_p : ∀ e, deg src tgt (src e) = 2 → hp e ≤ 3 / 4
  two_m : ∀ e, deg src tgt (tgt e) = 2 → hm e ≤ 3 / 4
  three_p : ∀ e, 3 ≤ deg src tgt (src e) → hp e ≤ 4 / ((deg src tgt (src e) : ℝ) + 3)
  three_m : ∀ e, 3 ≤ deg src tgt (tgt e) → hm e ≤ 4 / ((deg src tgt (tgt e) : ℝ) + 3)

namespace Darts

variable {src tgt : E → V} {hp hm : E → ℝ} (D : Darts src tgt hp hm)
include D

theorem hp_le_two_thirds (e : E) (h3 : 3 ≤ deg src tgt (src e)) : hp e ≤ 2 / 3 := by
  have h := D.three_p e h3
  have hd : (3:ℝ) ≤ deg src tgt (src e) := by exact_mod_cast h3
  have h' : 4 / ((deg src tgt (src e) : ℝ) + 3) ≤ 4 / (3 + 3) := by gcongr
  norm_num at h'
  linarith

theorem hm_le_two_thirds (e : E) (h3 : 3 ≤ deg src tgt (tgt e)) : hm e ≤ 2 / 3 := by
  have h := D.three_m e h3
  have hd : (3:ℝ) ≤ deg src tgt (tgt e) := by exact_mod_cast h3
  have h' : 4 / ((deg src tgt (tgt e) : ℝ) + 3) ≤ 4 / (3 + 3) := by gcongr
  norm_num at h'
  linarith

theorem hp_le (e : E) : hp e ≤ 3 / 4 := by
  rcases Nat.eq_or_lt_of_le (D.deg_ge (src e)) with h2 | h3
  · exact D.two_p e h2.symm
  · have := D.hp_le_two_thirds e h3
    linarith

theorem hm_le (e : E) : hm e ≤ 3 / 4 := by
  rcases Nat.eq_or_lt_of_le (D.deg_ge (tgt e)) with h2 | h3
  · exact D.two_m e h2.symm
  · have := D.hm_le_two_thirds e h3
    linarith

/-- `d_v − inSum v ≥ d_v/4`. -/
theorem P_ge (v : V) : (deg src tgt v : ℝ) / 4 ≤ (deg src tgt v : ℝ) - inSum src tgt hp hm v := by
  have := inSum_le src tgt hp hm v (3 / 4) (fun e _ => D.hp_le e) (fun e _ => D.hm_le e)
  linarith

theorem P_pos (v : V) : 0 < (deg src tgt v : ℝ) - inSum src tgt hp hm v := by
  have h := D.P_ge v
  have hd : (2:ℝ) ≤ deg src tgt v := by exact_mod_cast D.deg_ge v
  linarith

theorem q_pos (e : E) : 0 < hp e * hm e := mul_pos (D.pos_p e) (D.pos_m e)

theorem q_lt (e : E) : 0 < 1 - hp e * hm e := by
  have h := mul_le_mul (D.hp_le e) (D.hm_le e) (D.pos_m e).le (by norm_num : (0:ℝ) ≤ 3 / 4)
  linarith

theorem x_pos (v : V) : 0 < xOf src tgt hp hm v := by
  unfold xOf; exact one_div_pos.2 (D.P_pos v)

theorem x_mul_P (v : V) :
    xOf src tgt hp hm v * ((deg src tgt v : ℝ) - inSum src tgt hp hm v) = 1 := by
  unfold xOf; exact one_div_mul_cancel (D.P_pos v).ne'

/-- `h_{u→v} = (1 − q_e) x_u`. -/
theorem hp_eq (e : E) : hp e = (1 - hp e * hm e) * xOf src tgt hp hm (src e) := by
  linear_combination (-(hp e)) * D.x_mul_P (src e) + xOf src tgt hp hm (src e) * D.eq_p e

/-- `h_{v→u} = (1 − q_e) x_v`. -/
theorem hm_eq (e : E) : hm e = (1 - hp e * hm e) * xOf src tgt hp hm (tgt e) := by
  linear_combination (-(hm e)) * D.x_mul_P (tgt e) + xOf src tgt hp hm (tgt e) * D.eq_m e

theorem r_pos (e : E) : 0 < rOf hp hm e := div_pos (D.q_pos e) (D.q_lt e)

/-- `r_e = x_u · (the dart into u along e)`. -/
theorem r_eq_src (e : E) : rOf hp hm e = xOf src tgt hp hm (src e) * hm e := by
  unfold rOf
  rw [div_eq_iff (D.q_lt e).ne']
  linear_combination hm e * D.hp_eq e

/-- `r_e = x_v · (the dart into v along e)`. -/
theorem r_eq_tgt (e : E) : rOf hp hm e = xOf src tgt hp hm (tgt e) * hp e := by
  unfold rOf
  rw [div_eq_iff (D.q_lt e).ne']
  linear_combination hp e * D.hm_eq e

/-- **(I1).** -/
theorem I1 (e : E) :
    rOf hp hm e * (1 + rOf hp hm e) = xOf src tgt hp hm (src e) * xOf src tgt hp hm (tgt e) := by
  have hq := (D.q_lt e).ne'
  have hX : xOf src tgt hp hm (src e) = hp e / (1 - hp e * hm e) := by
    rw [eq_div_iff hq]; linear_combination -(D.hp_eq e)
  have hY : xOf src tgt hp hm (tgt e) = hm e / (1 - hp e * hm e) := by
    rw [eq_div_iff hq]; linear_combination -(D.hm_eq e)
  rw [hX, hY]
  unfold rOf
  field_simp
  ring

/-- **(I2).** -/
theorem I2 (v : V) :
    endSum src tgt (rOf hp hm) v = deg src tgt v * xOf src tgt hp hm v - 1 := by
  have h1 : ∑ e ∈ univ.filter (fun e => src e = v), rOf hp hm e
      = xOf src tgt hp hm v * ∑ e ∈ univ.filter (fun e => src e = v), hm e := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [D.r_eq_src e, (Finset.mem_filter.1 he).2]
  have h2 : ∑ e ∈ univ.filter (fun e => tgt e = v), rOf hp hm e
      = xOf src tgt hp hm v * ∑ e ∈ univ.filter (fun e => tgt e = v), hp e := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [D.r_eq_tgt e, (Finset.mem_filter.1 he).2]
  have hx := D.x_mul_P v
  have hin : inSum src tgt hp hm v
      = ∑ e ∈ univ.filter (fun e => tgt e = v), hp e
        + ∑ e ∈ univ.filter (fun e => src e = v), hm e := rfl
  rw [hin] at hx
  unfold endSum
  rw [h1, h2]
  linear_combination (-1 : ℝ) * hx

/-- If `m ≤ d_v − inSum v` then `m · x_v ≤ 1`. -/
theorem mul_x_le (v : V) {m : ℝ} (h : m ≤ (deg src tgt v : ℝ) - inSum src tgt hp hm v) :
    m * xOf src tgt hp hm v ≤ 1 := by
  have hx := D.x_mul_P v
  nlinarith [mul_le_mul_of_nonneg_right h (D.x_pos v).le]

/-- **Lemma on ranges, part (a): degree 2.** -/
theorem R2 (v : V) (h2 : deg src tgt v = 2) :
    xOf src tgt hp hm v - 1 / (deg src tgt v : ℝ) ≤ 1 := by
  have hin : inSum src tgt hp hm v ≤ 2 / 3 * deg src tgt v := by
    refine inSum_le src tgt hp hm v (2 / 3) (fun e he => ?_) (fun e he => ?_)
    · have h22 := D.no22 e
      have hge := D.deg_ge (src e)
      have ht : deg src tgt (tgt e) = 2 := by rw [he]; exact h2
      exact D.hp_le_two_thirds e (by omega)
    · have h22 := D.no22 e
      have hge := D.deg_ge (tgt e)
      have hs : deg src tgt (src e) = 2 := by rw [he]; exact h2
      exact D.hm_le_two_thirds e (by omega)
  have hd : (deg src tgt v : ℝ) = 2 := by exact_mod_cast h2
  have hmx := D.mul_x_le v (m := 2 / 3) (by rw [hd] at hin ⊢; linarith)
  rw [hd]
  linarith

/-- **Lemma on ranges, part (b): degree `d ≥ 3`.** -/
theorem R3 (v : V) (h3 : 3 ≤ deg src tgt v) :
    xOf src tgt hp hm v - 1 / (deg src tgt v : ℝ) ≤ 3 / (deg src tgt v : ℝ) := by
  have hd : (3:ℝ) ≤ deg src tgt v := by exact_mod_cast h3
  have hd0 : (0:ℝ) < deg src tgt v := by linarith
  have hmx := D.mul_x_le v (D.P_ge v)
  have hx : xOf src tgt hp hm v ≤ 4 / (deg src tgt v : ℝ) := by
    rw [le_div_iff₀ hd0]; linarith
  have e : 3 / (deg src tgt v : ℝ) = 4 / (deg src tgt v : ℝ) - 1 / (deg src tgt v : ℝ) := by ring
  rw [e]
  linarith

/-- **Lemma on ranges, part (c): degree `d ≥ 3` with a neighbour of degree `≥ 3`.** -/
theorem R3' (v : V) (h3 : 3 ≤ deg src tgt v)
    (hex : ∃ e, (src e = v ∧ 3 ≤ deg src tgt (tgt e)) ∨ (tgt e = v ∧ 3 ≤ deg src tgt (src e))) :
    xOf src tgt hp hm v - 1 / (deg src tgt v : ℝ) ≤ Rprime (deg src tgt v) := by
  have hin : inSum src tgt hp hm v ≤ 3 / 4 * deg src tgt v - 1 / 12 := by
    refine inSum_le_special src tgt hp hm v (3 / 4) (1 / 12) (fun e _ => D.hp_le e)
      (fun e _ => D.hm_le e) ?_
    obtain ⟨e, ⟨he, hd⟩ | ⟨he, hd⟩⟩ := hex
    · exact Or.inr ⟨e, he, by have := D.hm_le_two_thirds e hd; linarith⟩
    · exact Or.inl ⟨e, he, by have := D.hp_le_two_thirds e hd; linarith⟩
  have hd : (3:ℝ) ≤ deg src tgt v := by exact_mod_cast h3
  have hd0 : (0:ℝ) < deg src tgt v := by linarith
  have hmx := D.mul_x_le v (m := (3 * (deg src tgt v : ℝ) + 1) / 12) (by linarith)
  have hx : xOf src tgt hp hm v ≤ 12 / (3 * (deg src tgt v : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have e : Rprime (deg src tgt v)
      = 12 / (3 * (deg src tgt v : ℝ) + 1) - 1 / (deg src tgt v : ℝ) := by
    unfold Rprime; field_simp; ring
  rw [e]
  linarith

end Darts

/-- **The edge inequality for a dart function.** -/
theorem tree_entropy_bound_of_darts [Fintype V] {src tgt : E → V} {hp hm : E → ℝ}
    (D : Darts src tgt hp hm) :
    ∑ e, Real.log (1 + rOf hp hm e) - ∑ v, Real.log (xOf src tgt hp hm v)
      ≤ (Fintype.card E : ℝ) * (1 / 2 * Real.log (27 / 8)) :=
  tree_entropy_bound src tgt (xOf src tgt hp hm) (rOf hp hm) D.r_pos D.I1 D.I2 D.deg_ge D.no22
    D.R2 D.R3 D.R3'

/-- The same, written directly in the dart values. -/
theorem tree_entropy_bound_of_darts' [Fintype V] {src tgt : E → V} {hp hm : E → ℝ}
    (D : Darts src tgt hp hm) :
    ∑ v, Real.log ((deg src tgt v : ℝ) - inSum src tgt hp hm v)
        - ∑ e, Real.log (1 - hp e * hm e)
      ≤ (Fintype.card E : ℝ) * (1 / 2 * Real.log (27 / 8)) := by
  have h := tree_entropy_bound_of_darts D
  have hr : ∀ e, Real.log (1 + rOf hp hm e) = -Real.log (1 - hp e * hm e) := by
    intro e
    have hq := (D.q_lt e).ne'
    rw [← Real.log_inv]
    congr 1
    unfold rOf
    field_simp
    ring
  have hx : ∀ v, Real.log (xOf src tgt hp hm v)
      = -Real.log ((deg src tgt v : ℝ) - inSum src tgt hp hm v) := by
    intro v
    unfold xOf
    rw [one_div, Real.log_inv]
  simp only [hr, hx, Finset.sum_neg_distrib] at h
  linarith

end TreeEntropy
