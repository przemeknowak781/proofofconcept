import Kenyon.Levels

/-!
# Super-solutions of the dart system

A pair of dart functions is a *super-solution* at the parameter `a` if

    h_{u→v} · (d_u − a · Σ_{darts into u other than v→u} h) ≥ a      for every dart u → v.

* `superSol_sol` : the solution at `b` is a super-solution at every `a ≤ b`;
* `superSol_mix` : a convex combination of two `Good` super-solutions is a super-solution
  (the map `X ↦ a / (d − a X)` is convex);
* `SuperSol.grad_p`, `SuperSol.grad_m` : at a super-solution the partial derivatives of the Bethe
  functional are nonnegative, in the form
  `a · (1 − hp e · hm e) ≤ hm e · (d_{tgt e} − a · inSum (tgt e))` and the symmetric statement.
-/

open Finset

namespace Kenyon

open TreeEntropy

variable {V E : Type} [Fintype E] [DecidableEq V]

/-- Super-solutions of the dart system at the parameter `a`. -/
def SuperSol (src tgt : E → V) (a : ℝ) (hp hm : E → ℝ) : Prop :=
  (∀ e, a ≤ hp e * ((deg src tgt (src e) : ℝ) - a * othP src tgt hp hm e)) ∧
  (∀ e, a ≤ hm e * ((deg src tgt (tgt e) : ℝ) - a * othM src tgt hp hm e))

omit [Fintype E] [DecidableEq V] in
/-- `1/u` is convex: the harmonic mean is at most the arithmetic mean. -/
theorem inv_mix_le {u₀ u₁ s : ℝ} (h0 : 0 < u₀) (h1 : 0 < u₁) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    1 / ((1 - s) * u₀ + s * u₁) ≤ (1 - s) / u₀ + s / u₁ := by
  have hm : 0 < (1 - s) * u₀ + s * u₁ := by
    rcases hs1.eq_or_lt with rfl | hlt
    · simpa using h1
    · have : 0 < (1 - s) * u₀ := mul_pos (sub_pos.2 hlt) h0
      have : 0 ≤ s * u₁ := mul_nonneg hs0 h1.le
      linarith
  rw [div_add_div _ _ h0.ne' h1.ne', div_le_div_iff₀ hm (mul_pos h0 h1)]
  nlinarith [mul_nonneg (mul_nonneg hs0 (sub_nonneg.2 hs1)) (sq_nonneg (u₀ - u₁))]

omit [DecidableEq V] in
theorem inSum_mix [DecidableEq V] (src tgt : E → V) (hp hm hp' hm' : E → ℝ) (s : ℝ) (v : V) :
    inSum src tgt (fun e => (1 - s) * hp e + s * hp' e) (fun e => (1 - s) * hm e + s * hm' e) v
      = (1 - s) * inSum src tgt hp hm v + s * inSum src tgt hp' hm' v := by
  unfold inSum
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem othP_mix (src tgt : E → V) (hp hm hp' hm' : E → ℝ) (s : ℝ) (e : E) :
    othP src tgt (fun e => (1 - s) * hp e + s * hp' e) (fun e => (1 - s) * hm e + s * hm' e) e
      = (1 - s) * othP src tgt hp hm e + s * othP src tgt hp' hm' e := by
  unfold othP
  rw [inSum_mix]
  ring

theorem othM_mix (src tgt : E → V) (hp hm hp' hm' : E → ℝ) (s : ℝ) (e : E) :
    othM src tgt (fun e => (1 - s) * hp e + s * hp' e) (fun e => (1 - s) * hm e + s * hm' e) e
      = (1 - s) * othM src tgt hp hm e + s * othM src tgt hp' hm' e := by
  unfold othM
  rw [inSum_mix]
  ring

section ClassC

variable {src tgt : E → V} (hdeg : ∀ v, 2 ≤ deg src tgt v)
  (hD : ∀ e, ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2))

include hdeg hD in
/-- The solution at `b` is a super-solution at every `a ≤ b`. -/
theorem superSol_sol {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    SuperSol src tgt a (solP src tgt b) (solM src tgt b) := by
  have hb0 : 0 ≤ b := ha0.trans hab
  have G := sol_good hdeg hD hb0 hb1
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have hfix := sol_fix_p hdeg hD hb0 hb1 e
    have h0 := othP_nonneg src tgt G.1 G.2.1 e
    nlinarith [mul_nonneg (G.1 e) (mul_nonneg (sub_nonneg.2 hab) h0)]
  · have hfix := sol_fix_m hdeg hD hb0 hb1 e
    have h0 := othM_nonneg src tgt G.1 G.2.1 e
    nlinarith [mul_nonneg (G.2.1 e) (mul_nonneg (sub_nonneg.2 hab) h0)]

include hdeg in
/-- A convex combination of two `Good` super-solutions is a super-solution. -/
theorem superSol_mix {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {hp hm hp' hm' : E → ℝ}
    (G : Good src tgt hp hm) (G' : Good src tgt hp' hm') (S : SuperSol src tgt a hp hm)
    (S' : SuperSol src tgt a hp' hm') {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    SuperSol src tgt a (fun e => (1 - s) * hp e + s * hp' e)
      (fun e => (1 - s) * hm e + s * hm' e) := by
  refine ⟨fun e => ?_, fun e => ?_⟩
  · rw [othP_mix]
    set u₀ := (deg src tgt (src e) : ℝ) - a * othP src tgt hp hm e with hu₀
    set u₁ := (deg src tgt (src e) : ℝ) - a * othP src tgt hp' hm' e with hu₁
    have p0 : 0 < u₀ := G.denP_pos hdeg ha1 e
    have p1 : 0 < u₁ := G'.denP_pos hdeg ha1 e
    have e0 : a / u₀ ≤ hp e := by rw [div_le_iff₀ p0]; exact S.1 e
    have e1 : a / u₁ ≤ hp' e := by rw [div_le_iff₀ p1]; exact S'.1 e
    have hmix : 0 < (1 - s) * u₀ + s * u₁ := by
      rcases hs1.eq_or_lt with rfl | hlt
      · simpa using p1
      · have : 0 < (1 - s) * u₀ := mul_pos (sub_pos.2 hlt) p0
        have : 0 ≤ s * u₁ := mul_nonneg hs0 p1.le
        linarith
    have hconv := inv_mix_le p0 p1 hs0 hs1
    have key : a / ((1 - s) * u₀ + s * u₁) ≤ (1 - s) * hp e + s * hp' e := by
      calc a / ((1 - s) * u₀ + s * u₁) = a * (1 / ((1 - s) * u₀ + s * u₁)) := by ring
        _ ≤ a * ((1 - s) / u₀ + s / u₁) := mul_le_mul_of_nonneg_left hconv ha0
        _ = (1 - s) * (a / u₀) + s * (a / u₁) := by ring
        _ ≤ (1 - s) * hp e + s * hp' e :=
            add_le_add (mul_le_mul_of_nonneg_left e0 (sub_nonneg.2 hs1))
              (mul_le_mul_of_nonneg_left e1 hs0)
    rw [div_le_iff₀ hmix] at key
    have hden : (deg src tgt (src e) : ℝ)
        - a * ((1 - s) * othP src tgt hp hm e + s * othP src tgt hp' hm' e)
        = (1 - s) * u₀ + s * u₁ := by
      rw [hu₀, hu₁]; ring
    rw [hden]
    exact key
  · rw [othM_mix]
    set u₀ := (deg src tgt (tgt e) : ℝ) - a * othM src tgt hp hm e with hu₀
    set u₁ := (deg src tgt (tgt e) : ℝ) - a * othM src tgt hp' hm' e with hu₁
    have p0 : 0 < u₀ := G.denM_pos hdeg ha1 e
    have p1 : 0 < u₁ := G'.denM_pos hdeg ha1 e
    have e0 : a / u₀ ≤ hm e := by rw [div_le_iff₀ p0]; exact S.2 e
    have e1 : a / u₁ ≤ hm' e := by rw [div_le_iff₀ p1]; exact S'.2 e
    have hmix : 0 < (1 - s) * u₀ + s * u₁ := by
      rcases hs1.eq_or_lt with rfl | hlt
      · simpa using p1
      · have : 0 < (1 - s) * u₀ := mul_pos (sub_pos.2 hlt) p0
        have : 0 ≤ s * u₁ := mul_nonneg hs0 p1.le
        linarith
    have hconv := inv_mix_le p0 p1 hs0 hs1
    have key : a / ((1 - s) * u₀ + s * u₁) ≤ (1 - s) * hm e + s * hm' e := by
      calc a / ((1 - s) * u₀ + s * u₁) = a * (1 / ((1 - s) * u₀ + s * u₁)) := by ring
        _ ≤ a * ((1 - s) / u₀ + s / u₁) := mul_le_mul_of_nonneg_left hconv ha0
        _ = (1 - s) * (a / u₀) + s * (a / u₁) := by ring
        _ ≤ (1 - s) * hm e + s * hm' e :=
            add_le_add (mul_le_mul_of_nonneg_left e0 (sub_nonneg.2 hs1))
              (mul_le_mul_of_nonneg_left e1 hs0)
    rw [div_le_iff₀ hmix] at key
    have hden : (deg src tgt (tgt e) : ℝ)
        - a * ((1 - s) * othM src tgt hp hm e + s * othM src tgt hp' hm' e)
        = (1 - s) * u₀ + s * u₁ := by
      rw [hu₀, hu₁]; ring
    rw [hden]
    exact key

omit [DecidableEq V] in
/-- At a super-solution: `a (1 − hp e · hm e) ≤ hp e · (d_{src e} − a · inSum (src e))`. -/
theorem SuperSol.grad_p [DecidableEq V] {a : ℝ} {hp hm : E → ℝ}
    (S : SuperSol src tgt a hp hm) (e : E) :
    a * (1 - hp e * hm e)
      ≤ hp e * ((deg src tgt (src e) : ℝ) - a * inSum src tgt hp hm (src e)) := by
  have h := S.1 e
  unfold othP at h
  nlinarith

omit [DecidableEq V] in
/-- At a super-solution: `a (1 − hp e · hm e) ≤ hm e · (d_{tgt e} − a · inSum (tgt e))`. -/
theorem SuperSol.grad_m [DecidableEq V] {a : ℝ} {hp hm : E → ℝ}
    (S : SuperSol src tgt a hp hm) (e : E) :
    a * (1 - hp e * hm e)
      ≤ hm e * ((deg src tgt (tgt e) : ℝ) - a * inSum src tgt hp hm (tgt e)) := by
  have h := S.2 e
  unfold othM at h
  nlinarith

end ClassC

end Kenyon
