import Kenyon.Super

/-!
# The Bethe functional increases along super-solutions

`Pof z hp hm v = d_v − z · inSum v` and

    Bfun z hp hm = ∑ v, log (Pof z hp hm v) − ∑ e, log (1 − hp e · hm e).

`Bfun_mono`: if `(hp, hm) ≤ (hp', hm')` are two `Good` super-solutions at `a ∈ [0, 1]`, then
`Bfun a hp hm ≤ Bfun a hp' hm'`.

Proof: on the segment between the two points every point is a super-solution
(`superSol_mix`), and at a super-solution every partial derivative of `Bfun a` is nonnegative
(`SuperSol.grad_p`, `SuperSol.grad_m`); so the function `s ↦ Bfun a ((1 − s)·(hp, hm) + s·(hp', hm'))`
has a nonnegative derivative on `[0, 1]`.
-/

open Finset

namespace Kenyon

open TreeEntropy

variable {V E : Type} [Fintype E] [Fintype V] [DecidableEq V]

/-- `P_v = d_v − z · inSum v`. -/
def Pof (src tgt : E → V) (z : ℝ) (hp hm : E → ℝ) (v : V) : ℝ :=
  (deg src tgt v : ℝ) - z * inSum src tgt hp hm v

/-- The Bethe functional. -/
noncomputable def Bfun (src tgt : E → V) (z : ℝ) (hp hm : E → ℝ) : ℝ :=
  ∑ v, Real.log (Pof src tgt z hp hm v) - ∑ e, Real.log (1 - hp e * hm e)

omit [Fintype V] in
theorem Pof_mix (src tgt : E → V) (a : ℝ) (hp hm hp' hm' : E → ℝ) (s : ℝ) (v : V) :
    Pof src tgt a (fun e => (1 - s) * hp e + s * hp' e) (fun e => (1 - s) * hm e + s * hm' e) v
      = (1 - s) * Pof src tgt a hp hm v + s * Pof src tgt a hp' hm' v := by
  unfold Pof
  rw [inSum_mix]
  ring

omit [Fintype V] [DecidableEq V] in
theorem hasDerivAt_mix (c c' s : ℝ) :
    HasDerivAt (fun y : ℝ => (1 - y) * c + y * c') (c' - c) s := by
  have h1 : HasDerivAt (fun y : ℝ => (1 - y) * c) (-1 * c) s :=
    ((hasDerivAt_id' s).const_sub 1).mul_const c
  have h2 : HasDerivAt (fun y : ℝ => y * c') (1 * c') s := (hasDerivAt_id' s).mul_const c'
  have h := h1.fun_add h2
  convert h using 1
  ring

section ClassC

variable {src tgt : E → V} (hdeg : ∀ v, 2 ≤ deg src tgt v)

omit [Fintype V] in
theorem Good.inSum_nonneg {hp hm : E → ℝ} (G : Good src tgt hp hm) (v : V) :
    0 ≤ inSum src tgt hp hm v :=
  add_nonneg (Finset.sum_nonneg fun e _ => G.1 e) (Finset.sum_nonneg fun e _ => G.2.1 e)

omit [Fintype V] in
include hdeg in
theorem Good.inSum_le {hp hm : E → ℝ} (G : Good src tgt hp hm) (v : V) :
    inSum src tgt hp hm v ≤ 3 / 4 * deg src tgt v :=
  TreeEntropy.inSum_le src tgt hp hm v (3 / 4) (fun e _ => G.2.2.hp_le hdeg e)
    (fun e _ => G.2.2.hm_le hdeg e)

omit [Fintype V] in
include hdeg in
/-- `P_v ≥ d_v / 4 > 0` for `a ≤ 1`. -/
theorem Good.Pof_ge {hp hm : E → ℝ} (G : Good src tgt hp hm) {a : ℝ} (ha1 : a ≤ 1) (v : V) :
    (deg src tgt v : ℝ) / 4 ≤ Pof src tgt a hp hm v := by
  have h1 := G.inSum_le hdeg v
  have h0 := G.inSum_nonneg v
  unfold Pof
  nlinarith [mul_nonneg (sub_nonneg.2 ha1) h0]

omit [Fintype V] in
include hdeg in
theorem Good.Pof_pos {hp hm : E → ℝ} (G : Good src tgt hp hm) {a : ℝ} (ha1 : a ≤ 1) (v : V) :
    0 < Pof src tgt a hp hm v := by
  have h := G.Pof_ge hdeg ha1 v
  have hd : (2:ℝ) ≤ deg src tgt v := by exact_mod_cast hdeg v
  linarith

omit [Fintype V] in
include hdeg in
theorem Good.q_le {hp hm : E → ℝ} (G : Good src tgt hp hm) (e : E) : hp e * hm e ≤ 9 / 16 := by
  have h1 := G.2.2.hp_le hdeg e
  have h2 := G.2.2.hm_le hdeg e
  nlinarith [G.1 e, G.2.1 e]

include hdeg in
/-- **The Bethe functional increases along super-solutions.** -/
theorem Bfun_mono {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {hp hm hp' hm' : E → ℝ}
    (G : Good src tgt hp hm) (G' : Good src tgt hp' hm') (S : SuperSol src tgt a hp hm)
    (S' : SuperSol src tgt a hp' hm') (h1 : ∀ e, hp e ≤ hp' e) (h2 : ∀ e, hm e ≤ hm' e) :
    Bfun src tgt a hp hm ≤ Bfun src tgt a hp' hm' := by
  -- the segment
  set ps : ℝ → E → ℝ := fun s e => (1 - s) * hp e + s * hp' e with hps
  set ms : ℝ → E → ℝ := fun s e => (1 - s) * hm e + s * hm' e with hms
  set ψ : ℝ → ℝ := fun s => Bfun src tgt a (ps s) (ms s) with hψ
  have hψ0 : ψ 0 = Bfun src tgt a hp hm := by simp [hψ, hps, hms]
  have hψ1 : ψ 1 = Bfun src tgt a hp' hm' := by simp [hψ, hps, hms]
  -- positivity on the segment
  have Ppos : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ v, 0 < Pof src tgt a (ps s) (ms s) v := by
    intro s hs v
    rw [hps, hms, Pof_mix]
    have p0 := G.Pof_pos hdeg ha1 v
    have p1 := G'.Pof_pos hdeg ha1 v
    rcases hs.2.eq_or_lt with rfl | hlt
    · simpa using p1
    · have : 0 < (1 - s) * Pof src tgt a hp hm v := mul_pos (sub_pos.2 hlt) p0
      have : 0 ≤ s * Pof src tgt a hp' hm' v := mul_nonneg hs.1 p1.le
      linarith
  have psb : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ e, 0 ≤ ps s e ∧ ps s e ≤ 3 / 4 := by
    intro s hs e
    have a0 := G.1 e
    have a1 := G'.1 e
    have b0 := G.2.2.hp_le hdeg e
    have b1 := G'.2.2.hp_le hdeg e
    have hs1 : 0 ≤ 1 - s := sub_nonneg.2 hs.2
    constructor
    · exact add_nonneg (mul_nonneg hs1 a0) (mul_nonneg hs.1 a1)
    · show (1 - s) * hp e + s * hp' e ≤ 3 / 4
      nlinarith [mul_le_mul_of_nonneg_left b0 hs1, mul_le_mul_of_nonneg_left b1 hs.1]
  have msb : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ e, 0 ≤ ms s e ∧ ms s e ≤ 3 / 4 := by
    intro s hs e
    have a0 := G.2.1 e
    have a1 := G'.2.1 e
    have b0 := G.2.2.hm_le hdeg e
    have b1 := G'.2.2.hm_le hdeg e
    have hs1 : 0 ≤ 1 - s := sub_nonneg.2 hs.2
    constructor
    · exact add_nonneg (mul_nonneg hs1 a0) (mul_nonneg hs.1 a1)
    · show (1 - s) * hm e + s * hm' e ≤ 3 / 4
      nlinarith [mul_le_mul_of_nonneg_left b0 hs1, mul_le_mul_of_nonneg_left b1 hs.1]
  have Qpos : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ e, 0 < 1 - ps s e * ms s e := by
    intro s hs e
    obtain ⟨p0, p1⟩ := psb s hs e
    obtain ⟨m0, m1⟩ := msb s hs e
    nlinarith
  -- the derivative
  set D : ℝ → ℝ := fun s =>
    ∑ v, (Pof src tgt a hp' hm' v - Pof src tgt a hp hm v) / Pof src tgt a (ps s) (ms s) v
      - ∑ e, -((hp' e - hp e) * ms s e + ps s e * (hm' e - hm e)) / (1 - ps s e * ms s e)
    with hD
  have hderiv : ∀ s ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (D s) s := by
    intro s hs
    have e1 : ψ = fun y => ∑ v, Real.log ((1 - y) * Pof src tgt a hp hm v
        + y * Pof src tgt a hp' hm' v)
        - ∑ e, Real.log (1 - ((1 - y) * hp e + y * hp' e) * ((1 - y) * hm e + y * hm' e)) := by
      funext y
      simp only [hψ, Bfun, hps, hms, Pof_mix]
    rw [e1]
    have d1 : HasDerivAt (fun y => ∑ v, Real.log ((1 - y) * Pof src tgt a hp hm v
        + y * Pof src tgt a hp' hm' v))
        (∑ v, (Pof src tgt a hp' hm' v - Pof src tgt a hp hm v)
          / Pof src tgt a (ps s) (ms s) v) s := by
      apply HasDerivAt.fun_sum
      intro v _
      have hne : (1 - s) * Pof src tgt a hp hm v + s * Pof src tgt a hp' hm' v ≠ 0 := by
        have := Ppos s hs v
        rw [hps, hms, Pof_mix] at this
        exact this.ne'
      have := (hasDerivAt_mix (Pof src tgt a hp hm v) (Pof src tgt a hp' hm' v) s).log hne
      rwa [← Pof_mix] at this
    have d2 : HasDerivAt (fun y => ∑ e, Real.log (1 - ((1 - y) * hp e + y * hp' e)
        * ((1 - y) * hm e + y * hm' e)))
        (∑ e, -((hp' e - hp e) * ms s e + ps s e * (hm' e - hm e)) / (1 - ps s e * ms s e)) s := by
      apply HasDerivAt.fun_sum
      intro e _
      have hne : 1 - ((1 - s) * hp e + s * hp' e) * ((1 - s) * hm e + s * hm' e) ≠ 0 :=
        (Qpos s hs e).ne'
      exact (((hasDerivAt_mix (hp e) (hp' e) s).mul (hasDerivAt_mix (hm e) (hm' e) s)).const_sub
        1).log hne
    exact d1.sub d2
  -- the derivative is nonnegative
  have hDnn : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 ≤ D s := by
    intro s hs
    have SS := superSol_mix hdeg ha0 ha1 G G' S S' hs.1 hs.2
    have hlin : ∀ v, Pof src tgt a hp' hm' v - Pof src tgt a hp hm v
        = -(a * (∑ e ∈ univ.filter (fun e => tgt e = v), (hp' e - hp e)
          + ∑ e ∈ univ.filter (fun e => src e = v), (hm' e - hm e))) := by
      intro v
      unfold Pof inSum
      simp only [Finset.sum_sub_distrib]
      ring
    have hfirst : ∑ v, (Pof src tgt a hp' hm' v - Pof src tgt a hp hm v)
          / Pof src tgt a (ps s) (ms s) v
        = -(∑ e, (a / Pof src tgt a (ps s) (ms s) (tgt e)) * (hp' e - hp e)
          + ∑ e, (a / Pof src tgt a (ps s) (ms s) (src e)) * (hm' e - hm e)) := by
      rw [sum_fiber tgt (fun v => a / Pof src tgt a (ps s) (ms s) v) (fun e => hp' e - hp e),
        sum_fiber src (fun v => a / Pof src tgt a (ps s) (ms s) v) (fun e => hm' e - hm e),
        ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [hlin v]
      ring
    have hterm : ∀ e, 0 ≤ (hp' e - hp e) * (ms s e / (1 - ps s e * ms s e)
          - a / Pof src tgt a (ps s) (ms s) (tgt e))
        + (hm' e - hm e) * (ps s e / (1 - ps s e * ms s e)
          - a / Pof src tgt a (ps s) (ms s) (src e)) := by
      intro e
      have q := Qpos s hs e
      have pt := Ppos s hs (tgt e)
      have psrc := Ppos s hs (src e)
      have gm := SS.grad_m e
      have gp := SS.grad_p e
      have i1 : a / Pof src tgt a (ps s) (ms s) (tgt e) ≤ ms s e / (1 - ps s e * ms s e) := by
        rw [div_le_div_iff₀ pt q]
        have := gm
        unfold Pof
        simpa [hps, hms] using this
      have i2 : a / Pof src tgt a (ps s) (ms s) (src e) ≤ ps s e / (1 - ps s e * ms s e) := by
        rw [div_le_div_iff₀ psrc q]
        have := gp
        unfold Pof
        simpa [hps, hms] using this
      exact add_nonneg (mul_nonneg (sub_nonneg.2 (h1 e)) (sub_nonneg.2 i1))
        (mul_nonneg (sub_nonneg.2 (h2 e)) (sub_nonneg.2 i2))
    have hsum : D s = ∑ e, ((hp' e - hp e) * (ms s e / (1 - ps s e * ms s e)
          - a / Pof src tgt a (ps s) (ms s) (tgt e))
        + (hm' e - hm e) * (ps s e / (1 - ps s e * ms s e)
          - a / Pof src tgt a (ps s) (ms s) (src e))) := by
      rw [hD]
      simp only
      rw [hfirst, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      ring
    rw [hsum]
    exact Finset.sum_nonneg fun e _ => hterm e
  -- monotonicity
  have hmono : MonotoneOn ψ (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hderiv s ⟨hs.1.le, hs.2.le⟩).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hderiv s ⟨hs.1.le, hs.2.le⟩).deriv]
      exact hDnn s ⟨hs.1.le, hs.2.le⟩
  have := hmono (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  rwa [hψ0, hψ1] at this

end ClassC

end Kenyon
