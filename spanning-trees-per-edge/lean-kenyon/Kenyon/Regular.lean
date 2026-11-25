import Kenyon.OneStep

/-!
# 4-regular multigraphs: the constant solution of the dart system

For a multigraph in which every degree is `4` the levels of the dart system are constant,
`lev z t = (aLev z t, aLev z t)` with `aLev z 0 = 0`, `aLev z (t+1) = z / (4 − 3 z · aLev z t)`.
Their limit `sVal z` satisfies, for `0 ≤ z ≤ 1`,

* `sVal_fix`     : `sVal z · (4 − 3 z · sVal z) = z`;
* `sVal_le`      : `sVal z ≤ z / 3`;
* `sVal_one`     : `sVal 1 = 1/3`;
* `Xi_reg`, `Wsum_reg` : closed forms of `Xi z` and `Wsum z`;
* `Xi_one_reg`   : `Xi 1 = |V| · log (27/8)`;
* `Xi_step_reg`  : `Xi b − Xi a ≤ −(b − a) · Wsum a` for `0 ≤ a ≤ b ≤ 1`
  (the reverse of `Xi_step`; here the scalar function `h ↦ log (4 − 4bh) − 2 log (1 − h²)`
  decreases on `[0, sVal b]`).
-/

open Finset

namespace Kenyon

open TreeEntropy

/-- The scalar levels. -/
noncomputable def aLev (z : ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => z / (4 - 3 * z * aLev z t)

theorem aLev_bounds {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ∀ t, 0 ≤ aLev z t ∧ aLev z t ≤ z / 3
  | 0 => ⟨le_rfl, by positivity⟩
  | t + 1 => by
      obtain ⟨h0, h1⟩ := aLev_bounds hz0 hz1 t
      have hden : (3:ℝ) ≤ 4 - 3 * z * aLev z t := by
        nlinarith [mul_nonneg hz0 h0, mul_le_mul_of_nonneg_left h1 hz0]
      constructor
      · simp only [aLev]
        exact div_nonneg hz0 (by linarith)
      · simp only [aLev]
        exact div_le_div_of_nonneg_left hz0 (by norm_num) hden

/-- The limit of the scalar levels. -/
noncomputable def sVal (z : ℝ) : ℝ := ⨆ t, aLev z t

theorem sVal_le {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : sVal z ≤ z / 3 :=
  ciSup_le fun t => (aLev_bounds hz0 hz1 t).2

theorem sVal_nonneg {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ sVal z :=
  le_ciSup_of_le ⟨z / 3, by rintro _ ⟨t, rfl⟩; exact (aLev_bounds hz0 hz1 t).2⟩ 0 le_rfl

variable {V E : Type} [Fintype E] [DecidableEq V]

theorem inSum_const (src tgt : E → V) (a : ℝ) (v : V) :
    inSum src tgt (fun _ => a) (fun _ => a) v = a * deg src tgt v := by
  unfold inSum deg
  simp only [Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

variable {src tgt : E → V} (hreg : ∀ v, deg src tgt v = 4)

include hreg in
theorem lev_const (z : ℝ) : ∀ t, lev src tgt z t = (fun _ => aLev z t, fun _ => aLev z t)
  | 0 => rfl
  | t + 1 => by
      have ih := lev_const z t
      have h1 : ∀ e, stepP src tgt z (fun _ => aLev z t) (fun _ => aLev z t) e
          = aLev z (t + 1) := by
        intro e
        simp only [stepP, othP, inSum_const, hreg, aLev]
        congr 1
        push_cast
        ring
      have h2 : ∀ e, stepM src tgt z (fun _ => aLev z t) (fun _ => aLev z t) e
          = aLev z (t + 1) := by
        intro e
        simp only [stepM, othM, inSum_const, hreg, aLev]
        congr 1
        push_cast
        ring
      simp only [lev, ih]
      exact Prod.ext (funext h1) (funext h2)

include hreg in
theorem solP_reg (z : ℝ) : solP src tgt z = fun _ => sVal z := by
  funext e
  simp only [solP, sVal, lev_const hreg]

include hreg in
theorem solM_reg (z : ℝ) : solM src tgt z = fun _ => sVal z := by
  funext e
  simp only [solM, sVal, lev_const hreg]

include hreg in
theorem two_le_deg_reg (v : V) : 2 ≤ deg src tgt v := by
  rw [hreg]
  norm_num

include hreg in
theorem no22_reg (e : E) : ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2) := by
  rintro ⟨h, -⟩
  rw [hreg] at h
  norm_num at h

include hreg in
theorem exists_edge_reg (v : V) : ∃ e : E, src e = v ∨ tgt e = v := by
  have h := hreg v
  unfold deg at h
  by_contra hno
  have h1 : (univ.filter fun e => src e = v) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun e _ he => hno ⟨e, Or.inl he⟩
  have h2 : (univ.filter fun e => tgt e = v) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun e _ he => hno ⟨e, Or.inr he⟩
  rw [h1, h2] at h
  simp at h

include hreg in
theorem sVal_fix (v₀ : V) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    sVal z * (4 - 3 * z * sVal z) = z := by
  obtain ⟨e, -⟩ := exists_edge_reg hreg v₀
  have h := sol_fix_p (two_le_deg_reg hreg) (no22_reg hreg) hz0 hz1 e
  rw [solP_reg hreg, solM_reg hreg] at h
  simp only [othP, inSum_const, hreg] at h
  push_cast at h
  calc sVal z * (4 - 3 * z * sVal z) = sVal z * (4 - z * (sVal z * 4 - sVal z)) := by ring
    _ = z := h

include hreg in
theorem sVal_mono (v₀ : V) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    sVal a ≤ sVal b := by
  obtain ⟨e, -⟩ := exists_edge_reg hreg v₀
  have h := (sol_mono_z (two_le_deg_reg hreg) (no22_reg hreg) ha0 hab hb1).1 e
  rwa [solP_reg hreg, solP_reg hreg] at h

include hreg in
theorem sVal_one (v₀ : V) : sVal 1 = 1 / 3 := by
  have h := sVal_fix hreg v₀ zero_le_one (le_refl (1:ℝ))
  have h1 := sVal_le zero_le_one (le_refl (1:ℝ))
  have h2 : (3 * sVal 1 - 1) * (sVal 1 - 1) = 0 := by nlinarith
  rcases mul_eq_zero.1 h2 with h3 | h3
  · linarith
  · linarith

variable [Fintype V]

include hreg in
/-- Handshake: `|E| = 2 |V|`. -/
theorem card_edges_reg : Fintype.card E = 2 * Fintype.card V := by
  classical
  have h1 : Fintype.card E = ∑ v : V, (univ.filter fun e : E => src e = v).card :=
    Finset.card_eq_sum_card_fiberwise (f := src) (s := univ) (t := univ)
      (fun _ _ => Finset.mem_univ _)
  have h2 : Fintype.card E = ∑ v : V, (univ.filter fun e : E => tgt e = v).card :=
    Finset.card_eq_sum_card_fiberwise (f := tgt) (s := univ) (t := univ)
      (fun _ _ => Finset.mem_univ _)
  have h3 : ∑ v : V, deg src tgt v = 4 * Fintype.card V := by
    simp [hreg, mul_comm]
  have h4 : ∑ v : V, deg src tgt v = Fintype.card E + Fintype.card E := by
    unfold deg
    rw [Finset.sum_add_distrib, ← h1, ← h2]
  omega

omit [Fintype V] in
include hreg in
theorem Pof_reg (z : ℝ) (v : V) :
    Pof src tgt z (solP src tgt z) (solM src tgt z) v = 4 - 4 * z * sVal z := by
  rw [solP_reg hreg, solM_reg hreg]
  unfold Pof
  rw [inSum_const, hreg]
  push_cast
  ring

include hreg in
theorem Xi_reg (z : ℝ) :
    Xi src tgt z = (Fintype.card V : ℝ) * Real.log (4 - 4 * z * sVal z)
      - (Fintype.card E : ℝ) * Real.log (1 - sVal z * sVal z) := by
  unfold Xi Bfun
  simp only [Pof_reg hreg]
  rw [solP_reg hreg, solM_reg hreg]
  simp [Finset.sum_const, nsmul_eq_mul]

include hreg in
theorem Wsum_reg (z : ℝ) :
    Wsum src tgt z = (Fintype.card V : ℝ) * (4 * sVal z / (4 - 4 * z * sVal z)) := by
  unfold Wsum
  simp only [Pof_reg hreg]
  rw [solP_reg hreg, solM_reg hreg]
  simp only [inSum_const, hreg, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  push_cast
  ring

include hreg in
theorem Xi_one_reg (v₀ : V) :
    Xi src tgt 1 = (Fintype.card V : ℝ) * Real.log (27 / 8) := by
  rw [Xi_reg hreg, sVal_one hreg v₀, card_edges_reg hreg]
  have h1 : (4 - 4 * 1 * (1 / 3) : ℝ) = 27 / 8 * (8 / 9) ^ 2 := by norm_num
  have h2 : (1 - 1 / 3 * (1 / 3) : ℝ) = 8 / 9 := by norm_num
  rw [h1, h2, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast
  ring

include hreg in
/-- **The scalar one-step inequality**, reverse to `Xi_step`. -/
theorem Xi_step_reg (v₀ : V) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    Xi src tgt b - Xi src tgt a ≤ -((b - a) * Wsum src tgt a) := by
  have hb0 := ha0.trans hab
  have ha1 := hab.trans hb1
  set sa := sVal a with hsa
  set sb := sVal b with hsb
  have sa0 : 0 ≤ sa := sVal_nonneg ha0 ha1
  have sb0 : 0 ≤ sb := sVal_nonneg hb0 hb1
  have sa3 : sa ≤ a / 3 := sVal_le ha0 ha1
  have sb3 : sb ≤ b / 3 := sVal_le hb0 hb1
  have hmono : sa ≤ sb := sVal_mono hreg v₀ ha0 hab hb1
  have hfix : sb * (4 - 3 * b * sb) = b := sVal_fix hreg v₀ hb0 hb1
  -- the scalar function
  set φ : ℝ → ℝ := fun h => Real.log (4 - 4 * b * h) - 2 * Real.log (1 - h ^ 2) with hφ
  have hpos : ∀ h ∈ Set.Icc (0:ℝ) sb, 0 < 4 - 4 * b * h ∧ 0 < 1 - h ^ 2 := by
    intro h hh
    have h3 : h ≤ 1 / 3 := by linarith [hh.2]
    constructor
    · nlinarith [mul_nonneg hb0 hh.1, mul_le_mul_of_nonneg_left h3 hb0]
    · nlinarith [hh.1]
  have hderiv : ∀ h ∈ Set.Icc (0:ℝ) sb,
      HasDerivAt φ (-(4 * b) / (4 - 4 * b * h) - 2 * (-(2 * h) / (1 - h ^ 2))) h := by
    intro h hh
    obtain ⟨p1, p2⟩ := hpos h hh
    have d1 : HasDerivAt (fun h : ℝ => 4 - 4 * b * h) (-(4 * b)) h := by
      have := ((hasDerivAt_id' h).const_mul (4 * b)).const_sub 4
      convert this using 1
      ring
    have d2 : HasDerivAt (fun h : ℝ => 1 - h ^ 2) (-(2 * h)) h := by
      have := (hasDerivAt_pow 2 h).const_sub 1
      convert this using 1
      norm_num
    exact (d1.log p1.ne').sub ((d2.log p2.ne').const_mul 2)
  have hnonpos : ∀ h ∈ Set.Icc (0:ℝ) sb,
      -(4 * b) / (4 - 4 * b * h) - 2 * (-(2 * h) / (1 - h ^ 2)) ≤ 0 := by
    intro h hh
    obtain ⟨p1, p2⟩ := hpos h hh
    have h3 : h ≤ 1 / 3 := by linarith [hh.2]
    have hq : 0 ≤ 3 * b * h ^ 2 - 4 * h + b := by
      have e1 : 3 * b * h ^ 2 - 4 * h + b = (h - sb) * (3 * b * (h + sb) - 4) := by
        nlinarith [hfix]
      rw [e1]
      apply mul_nonneg_of_nonpos_of_nonpos
      · linarith [hh.2]
      · nlinarith [mul_nonneg hb0 hh.1, mul_nonneg hb0 sb0,
          mul_le_mul_of_nonneg_left h3 hb0, mul_le_mul_of_nonneg_left (by linarith : sb ≤ 1 / 3) hb0]
    have e2 : -(4 * b) / (4 - 4 * b * h) - 2 * (-(2 * h) / (1 - h ^ 2))
        = -(4 * (3 * b * h ^ 2 - 4 * h + b)) / ((4 - 4 * b * h) * (1 - h ^ 2)) := by
      have n1 := p1.ne'
      have n2 := p2.ne'
      rw [eq_div_iff (mul_ne_zero n1 n2)]
      have c1 : -(4 * b) / (4 - 4 * b * h) * (4 - 4 * b * h) = -(4 * b) := div_mul_cancel₀ _ n1
      have c2 : -(2 * h) / (1 - h ^ 2) * (1 - h ^ 2) = -(2 * h) := div_mul_cancel₀ _ n2
      calc (-(4 * b) / (4 - 4 * b * h) - 2 * (-(2 * h) / (1 - h ^ 2)))
            * ((4 - 4 * b * h) * (1 - h ^ 2))
          = (-(4 * b) / (4 - 4 * b * h) * (4 - 4 * b * h)) * (1 - h ^ 2)
            - 2 * (-(2 * h) / (1 - h ^ 2) * (1 - h ^ 2)) * (4 - 4 * b * h) := by ring
        _ = -(4 * (3 * b * h ^ 2 - 4 * h + b)) := by
            rw [c1, c2]
            ring
    rw [e2]
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · exact (mul_pos p1 p2).le
  have hanti : AntitoneOn φ (Set.Icc 0 sb) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 sb)
    · exact fun h hh => (hderiv h hh).continuousAt.continuousWithinAt
    · intro h hh
      rw [interior_Icc] at hh
      exact (hderiv h ⟨hh.1.le, hh.2.le⟩).differentiableAt.differentiableWithinAt
    · intro h hh
      rw [interior_Icc] at hh
      rw [(hderiv h ⟨hh.1.le, hh.2.le⟩).deriv]
      exact hnonpos h ⟨hh.1.le, hh.2.le⟩
  have hφle : φ sb ≤ φ sa := hanti ⟨sa0, hmono⟩ ⟨sb0, le_rfl⟩ hmono
  -- the change of the parameter at fixed `sa`
  have pa : 0 < 4 - 4 * a * sa := by
    nlinarith [mul_nonneg ha0 sa0, mul_le_mul_of_nonneg_left sa3 ha0]
  have pb : 0 < 4 - 4 * b * sa := by
    nlinarith [mul_nonneg hb0 sa0, mul_le_mul_of_nonneg_left sa3 hb0]
  have hlog : Real.log (4 - 4 * b * sa) - Real.log (4 - 4 * a * sa)
      ≤ -((b - a) * (4 * sa / (4 - 4 * a * sa))) := by
    have h := Real.log_le_sub_one_of_pos (div_pos pb pa)
    rw [Real.log_div pb.ne' pa.ne'] at h
    have e : (4 - 4 * b * sa) / (4 - 4 * a * sa) - 1
        = -((b - a) * (4 * sa / (4 - 4 * a * sa))) := by
      have na := pa.ne'
      rw [div_sub_one na, mul_div_assoc', neg_div', div_left_inj₀ na]
      ring
    linarith
  rw [Xi_reg hreg, Xi_reg hreg, Wsum_reg hreg, card_edges_reg hreg]
  have hn : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  simp only [hφ] at hφle
  push_cast
  have e3 : sb * sb = sb ^ 2 := by ring
  have e4 : sa * sa = sa ^ 2 := by ring
  rw [← hsa, ← hsb, e3, e4]
  nlinarith [mul_le_mul_of_nonneg_left hφle hn, mul_le_mul_of_nonneg_left hlog hn]

end Kenyon
