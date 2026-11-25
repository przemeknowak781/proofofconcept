import Kenyon.OneStep
import Kenyon.Green
import Kenyon.LogDet

/-!
# The matrices `L`, `A`, `K(z) = D − zA` and the one-step inequality for `det K(z)`

* `inc e` is the incidence vector of the edge `e` (`+1` at `tgt e`, `−1` at `src e`, `0` for a loop);
* `lap = ∑ e, inc e ⊗ inc e` is the Laplacian, `Amat = D − lap` the adjacency matrix,
  `Kmat z = (1 − z) D + z · lap = D − z · Amat`;
* `Kmat_mulVec`    : `Kmat z *ᵥ g = Kop z g`;
* `Kmat_posDef`    : `Kmat z` is positive definite for `0 ≤ z < 1` when every degree is positive;
* `trace_inv_mul_Amat_ge` : `Wsum a ≤ tr (K(a)⁻¹ A)` (Green comparison);
* `det_Kmat_step`  : `det K(b) ≤ det K(a) · exp (−(b − a) · Wsum a)` for `0 ≤ a ≤ b < 1`.
-/

open Matrix Finset

namespace Kenyon

open TreeEntropy

variable {V E : Type} [Fintype E] [Fintype V] [DecidableEq V]

/-- The incidence vector of an edge. -/
def inc (src tgt : E → V) (e : E) (a : V) : ℝ :=
  (if tgt e = a then 1 else 0) - (if src e = a then 1 else 0)

/-- The Laplacian. -/
def lap (src tgt : E → V) : Matrix V V ℝ :=
  ∑ e, vecMulVec (inc src tgt e) (inc src tgt e)

/-- The adjacency matrix (a loop counts twice on the diagonal). -/
def Amat (src tgt : E → V) : Matrix V V ℝ :=
  diagonal (fun v => (deg src tgt v : ℝ)) - lap src tgt

/-- `K(z) = (1 − z) D + z L = D − z A`. -/
def Kmat (src tgt : E → V) (z : ℝ) : Matrix V V ℝ :=
  diagonal (fun v => (1 - z) * (deg src tgt v : ℝ)) + z • lap src tgt

omit [Fintype E] in
theorem inc_dot (src tgt : E → V) (e : E) (g : V → ℝ) :
    ∑ y, inc src tgt e y * g y = g (tgt e) - g (src e) := by
  simp [inc, sub_mul, Finset.sum_sub_distrib]

theorem lap_mulVec (src tgt : E → V) (g : V → ℝ) (x : V) :
    (lap src tgt *ᵥ g) x = (deg src tgt x : ℝ) * g x - nbSum src tgt g x := by
  have h1 : (lap src tgt *ᵥ g) x = ∑ e, inc src tgt e x * (g (tgt e) - g (src e)) := by
    simp only [mulVec, dotProduct, lap, Matrix.sum_apply, vecMulVec_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← inc_dot, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have a1 : ∑ e ∈ univ.filter (fun e => tgt e = x), (g (tgt e) - g (src e))
      = ((univ.filter fun e => tgt e = x).card : ℝ) * g x
        - ∑ e ∈ univ.filter (fun e => tgt e = x), g (src e) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_congr rfl (fun e he => by rw [(Finset.mem_filter.1 he).2] :
      ∀ e ∈ univ.filter (fun e => tgt e = x), g (tgt e) = g x)]
    simp
  have a2 : ∑ e ∈ univ.filter (fun e => src e = x), (g (tgt e) - g (src e))
      = ∑ e ∈ univ.filter (fun e => src e = x), g (tgt e)
        - ((univ.filter fun e => src e = x).card : ℝ) * g x := by
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_congr rfl (fun e he => by rw [(Finset.mem_filter.1 he).2] :
      ∀ e ∈ univ.filter (fun e => src e = x), g (src e) = g x)]
    simp
  have h2 : ∑ e, inc src tgt e x * (g (tgt e) - g (src e))
      = ∑ e ∈ univ.filter (fun e => tgt e = x), (g (tgt e) - g (src e))
        - ∑ e ∈ univ.filter (fun e => src e = x), (g (tgt e) - g (src e)) := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    unfold inc
    split_ifs <;> ring
  rw [h1, h2, a1, a2]
  unfold deg nbSum
  push_cast
  ring

theorem Kmat_mulVec (src tgt : E → V) (z : ℝ) (g : V → ℝ) (x : V) :
    (Kmat src tgt z *ᵥ g) x = Kop src tgt z g x := by
  unfold Kmat Kop
  rw [add_mulVec, Pi.add_apply, mulVec_diagonal, smul_mulVec, Pi.smul_apply, lap_mulVec,
    smul_eq_mul]
  ring

theorem Amat_mulVec (src tgt : E → V) (g : V → ℝ) (x : V) :
    (Amat src tgt *ᵥ g) x = nbSum src tgt g x := by
  unfold Amat
  rw [sub_mulVec, Pi.sub_apply, mulVec_diagonal, lap_mulVec]
  ring

omit [Fintype V] in
theorem lap_posSemidef (src tgt : E → V) : (lap src tgt).PosSemidef := by
  unfold lap
  exact posSemidef_sum _ fun e _ => by
    simpa using posSemidef_vecMulVec_self_star (inc src tgt e)

omit [Fintype V] in
theorem Kmat_posDef {src tgt : E → V} (hdeg : ∀ v, 1 ≤ deg src tgt v) {z : ℝ} (hz0 : 0 ≤ z)
    (hz1 : z < 1) : (Kmat src tgt z).PosDef :=
  (PosDef.diagonal fun v => mul_pos (sub_pos.2 hz1)
    (by exact_mod_cast hdeg v)).add_posSemidef ((lap_posSemidef src tgt).smul hz0)

theorem Kmat_zero_det (src tgt : E → V) :
    (Kmat src tgt 0).det = ∏ v, (deg src tgt v : ℝ) := by
  unfold Kmat
  simp

omit [Fintype V] in
theorem Kmat_eq_sub (src tgt : E → V) (a b : ℝ) :
    Kmat src tgt b = Kmat src tgt a - (b - a) • Amat src tgt := by
  unfold Kmat Amat
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply,
    smul_eq_mul]
  split_ifs <;> ring

section ClassC

variable {src tgt : E → V} (hdeg : ∀ v, 2 ≤ deg src tgt v)
  (hD : ∀ e, ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2))

include hdeg hD in
/-- **Green comparison in trace form.** -/
theorem trace_inv_mul_Amat_ge {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Wsum src tgt a ≤ ((Kmat src tgt a)⁻¹ * Amat src tgt).trace := by
  have hdeg1 : ∀ v, 1 ≤ deg src tgt v := fun v => le_trans (by norm_num) (hdeg v)
  have hM := Kmat_posDef hdeg1 ha0 ha1
  have hunit : IsUnit (Kmat src tgt a).det := hM.det_pos.ne'.isUnit
  have G := sol_good hdeg hD ha0 ha1.le
  rw [trace_mul_comm]
  unfold Wsum trace
  refine Finset.sum_le_sum fun v _ => ?_
  set g : V → ℝ := fun u => (Kmat src tgt a)⁻¹ u v with hg
  have hgA : (Amat src tgt * (Kmat src tgt a)⁻¹).diag v = nbSum src tgt g v := by
    rw [← Amat_mulVec]
    simp [Matrix.mul_apply, mulVec, dotProduct, hg]
  have hgcol : g = (Kmat src tgt a)⁻¹ *ᵥ Pi.single v 1 := by
    ext u
    simp [hg]
  have hKg : ∀ x, Kop src tgt a g x = if x = v then 1 else 0 := by
    intro x
    rw [← Kmat_mulVec, hgcol, mulVec_mulVec, mul_nonsing_inv _ hunit, one_mulVec,
      Pi.single_apply]
  have hK : ∀ x, 0 ≤ Kop src tgt a g x := by
    intro x
    rw [hKg]
    split_ifs <;> norm_num
  have g0 : ∀ x, 0 ≤ g x := fun x => nonneg_of_Kop_nonneg hdeg1 ha0 ha1 hK x
  obtain ⟨d1, d2⟩ := dart_ineq_sol hdeg hD ha0 ha1.le g0 hK
  have hgreen := green_sol hdeg hD ha0 ha1.le g0 hK v
  have hKv : Kop src tgt a g v = 1 := by rw [hKg]; simp
  rw [hKv] at hgreen
  have hnb := inSum_mul_le_nbSum src tgt (solP src tgt a) (solM src tgt a) g v
    (fun e he => by have := d1 e; rwa [he] at this)
    (fun e he => by have := d2 e; rwa [he] at this)
  have hP := G.Pof_pos hdeg ha1.le v
  have hS := G.inSum_nonneg v
  rw [hgA]
  have h1 : 1 / Pof src tgt a (solP src tgt a) (solM src tgt a) v ≤ g v := by
    rw [div_le_iff₀ hP]
    unfold Pof
    linarith
  calc inSum src tgt (solP src tgt a) (solM src tgt a) v
        / Pof src tgt a (solP src tgt a) (solM src tgt a) v
      = inSum src tgt (solP src tgt a) (solM src tgt a) v
        * (1 / Pof src tgt a (solP src tgt a) (solM src tgt a) v) := by ring
    _ ≤ inSum src tgt (solP src tgt a) (solM src tgt a) v * g v :=
        mul_le_mul_of_nonneg_left h1 hS
    _ ≤ nbSum src tgt g v := hnb

include hdeg hD in
/-- **One step for the determinant.** -/
theorem det_Kmat_step {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b < 1) :
    (Kmat src tgt b).det
      ≤ (Kmat src tgt a).det * Real.exp (-((b - a) * Wsum src tgt a)) := by
  have hdeg1 : ∀ v, 1 ≤ deg src tgt v := fun v => le_trans (by norm_num) (hdeg v)
  have ha1 := hab.trans_lt hb1
  have hM := Kmat_posDef hdeg1 ha0 ha1
  have hN := (Kmat_posDef hdeg1 (ha0.trans hab) hb1).posSemidef
  have h := det_le_det_mul_exp hM hN
  have hunit : IsUnit (Kmat src tgt a).det := hM.det_pos.ne'.isUnit
  have htr : ((Kmat src tgt a)⁻¹ * Kmat src tgt b).trace - Fintype.card V
      = -((b - a) * ((Kmat src tgt a)⁻¹ * Amat src tgt).trace) := by
    rw [Kmat_eq_sub src tgt a b, Matrix.mul_sub, nonsing_inv_mul _ hunit, trace_sub,
      Matrix.mul_smul, trace_smul, trace_one, smul_eq_mul]
    ring
  rw [htr] at h
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM.det_pos.le)
  have := trace_inv_mul_Amat_ge hdeg hD ha0 ha1
  nlinarith [sub_nonneg.2 hab]

end ClassC

end Kenyon
