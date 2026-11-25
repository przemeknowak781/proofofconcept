import Kenyon.BetheFun

/-!
# The Bethe value `Xi z` and its one-step inequality

`Xi z = Bfun z (solution at z)` and `Wsum z = ∑ v, S_v(z) / P_v(z)` with `S_v = inSum` of the
solution.

* `Xi_zero`  : `Xi 0 = ∑ v, log d_v`;
* `Xi_step`  : `−(b − a) · Wsum b ≤ Xi b − Xi a` for `0 ≤ a ≤ b ≤ 1`;
* `Wsum_le`  : `Wsum z ≤ 3 · |V|`;
* `Xi_le_one`: `Xi z ≤ Xi 1 + 3 · |V| · (1 − z)`.
-/

open Finset

namespace Kenyon

open TreeEntropy

variable {V E : Type} [Fintype E] [Fintype V] [DecidableEq V]

/-- The Bethe value at `z`. -/
noncomputable def Xi (src tgt : E → V) (z : ℝ) : ℝ :=
  Bfun src tgt z (solP src tgt z) (solM src tgt z)

/-- `∑ v, S_v(z) / P_v(z)`. -/
noncomputable def Wsum (src tgt : E → V) (z : ℝ) : ℝ :=
  ∑ v, inSum src tgt (solP src tgt z) (solM src tgt z) v
    / Pof src tgt z (solP src tgt z) (solM src tgt z) v

section ClassC

variable {src tgt : E → V} (hdeg : ∀ v, 2 ≤ deg src tgt v)
  (hD : ∀ e, ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2))

omit [Fintype V] in
include hdeg hD in
theorem sol_zero : (∀ e, solP src tgt 0 e = 0) ∧ (∀ e, solM src tgt 0 e = 0) := by
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have h := sol_fix_p hdeg hD le_rfl zero_le_one e
    have hd : (2:ℝ) ≤ deg src tgt (src e) := by exact_mod_cast hdeg (src e)
    rcases mul_eq_zero.1 h with h | h
    · exact h
    · linarith
  · have h := sol_fix_m hdeg hD le_rfl zero_le_one e
    have hd : (2:ℝ) ≤ deg src tgt (tgt e) := by exact_mod_cast hdeg (tgt e)
    rcases mul_eq_zero.1 h with h | h
    · exact h
    · linarith

include hdeg hD in
theorem Xi_zero : Xi src tgt 0 = ∑ v, Real.log (deg src tgt v) := by
  obtain ⟨h1, h2⟩ := sol_zero hdeg hD
  unfold Xi Bfun Pof
  simp [h1]

include hdeg hD in
theorem Wsum_nonneg {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ Wsum src tgt z := by
  have G := sol_good hdeg hD hz0 hz1
  exact Finset.sum_nonneg fun v _ => div_nonneg (G.inSum_nonneg v) (G.Pof_pos hdeg hz1 v).le

include hdeg hD in
theorem Wsum_le {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Wsum src tgt z ≤ 3 * Fintype.card V := by
  have G := sol_good hdeg hD hz0 hz1
  have h : ∀ v ∈ (univ : Finset V), inSum src tgt (solP src tgt z) (solM src tgt z) v
      / Pof src tgt z (solP src tgt z) (solM src tgt z) v ≤ 3 := by
    intro v _
    rw [div_le_iff₀ (G.Pof_pos hdeg hz1 v)]
    have a1 := G.inSum_le hdeg v
    have a2 := G.Pof_ge hdeg hz1 v
    linarith
  calc Wsum src tgt z ≤ ∑ _v : V, (3:ℝ) := Finset.sum_le_sum h
    _ = 3 * Fintype.card V := by simp [mul_comm]

include hdeg hD in
/-- **One step for the Bethe value.** -/
theorem Xi_step {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    -((b - a) * Wsum src tgt b) ≤ Xi src tgt b - Xi src tgt a := by
  have hb0 := ha0.trans hab
  have ha1 := hab.trans hb1
  have Ga := sol_good hdeg hD ha0 ha1
  have Gb := sol_good hdeg hD hb0 hb1
  have mono := sol_mono_z hdeg hD ha0 hab hb1
  have h2 : Bfun src tgt a (solP src tgt a) (solM src tgt a)
      ≤ Bfun src tgt a (solP src tgt b) (solM src tgt b) :=
    Bfun_mono hdeg ha0 ha1 Ga Gb (superSol_sol hdeg hD ha0 le_rfl ha1)
      (superSol_sol hdeg hD ha0 hab hb1) mono.1 mono.2
  have h1 : -((b - a) * Wsum src tgt b) ≤ Bfun src tgt b (solP src tgt b) (solM src tgt b)
      - Bfun src tgt a (solP src tgt b) (solM src tgt b) := by
    have hv : ∀ v ∈ (univ : Finset V),
        -((b - a) * (inSum src tgt (solP src tgt b) (solM src tgt b) v
          / Pof src tgt b (solP src tgt b) (solM src tgt b) v))
        ≤ Real.log (Pof src tgt b (solP src tgt b) (solM src tgt b) v)
          - Real.log (Pof src tgt a (solP src tgt b) (solM src tgt b) v) := by
      intro v _
      have pb := Gb.Pof_pos hdeg hb1 v
      have pa := Gb.Pof_pos hdeg ha1 v
      have hrel : Pof src tgt a (solP src tgt b) (solM src tgt b) v
          = Pof src tgt b (solP src tgt b) (solM src tgt b) v
            + (b - a) * inSum src tgt (solP src tgt b) (solM src tgt b) v := by
        unfold Pof; ring
      have hlog := Real.log_le_sub_one_of_pos (div_pos pa pb)
      rw [Real.log_div pa.ne' pb.ne'] at hlog
      have : Pof src tgt a (solP src tgt b) (solM src tgt b) v
          / Pof src tgt b (solP src tgt b) (solM src tgt b) v - 1
          = (b - a) * (inSum src tgt (solP src tgt b) (solM src tgt b) v
            / Pof src tgt b (solP src tgt b) (solM src tgt b) v) := by
        rw [hrel]; field_simp; ring
      linarith
    have hs := Finset.sum_le_sum hv
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hs
    unfold Bfun Wsum
    linarith
  unfold Xi
  linarith

include hdeg hD in
theorem Xi_le_one {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Xi src tgt z ≤ Xi src tgt 1 + 3 * Fintype.card V * (1 - z) := by
  have h := Xi_step hdeg hD hz0 hz1 le_rfl
  have hW := Wsum_le hdeg hD zero_le_one (le_refl (1:ℝ))
  nlinarith [mul_le_mul_of_nonneg_left hW (sub_nonneg.2 hz1)]

end ClassC

end Kenyon
