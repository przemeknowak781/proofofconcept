import Kenyon.Levels

/-!
# Comparison of the Green function with the dart solution

`Kop z g = (D − zA) g` is the operator of the graph: `(Kop z g) x = d_x · g x − z · Σ_{y ∼ x} g y`
(neighbours with multiplicity).

* `nonneg_of_Kop_nonneg` (maximum principle): for `0 ≤ z < 1` and positive degrees, `Kop z g ≥ 0`
  implies `g ≥ 0`.
* `dart_ineq`: if `g ≥ 0` and `Kop z g ≥ 0`, then `g u ≥ h⁽ˢ⁾_{u→v} · g v` for every dart `u → v`
  and every level `s`.  Proof by induction on `s`, from the equation at `u` only.
* `green_lev`, `green_sol`: hence `(Kop z g) v ≤ (d_v − z · inSum v) · g v`, at every level and for
  the limit.  If `g` is the column `v` of the inverse of `D − zA` (so `Kop z g = δ_v`), this says
  `(D − zA)⁻¹_{vv} ≥ 1 / (d_v − z · inSum v)`: the Green function of the graph is at least the
  Green function of its universal cover.  The cover itself does not appear.
-/

open Finset

namespace Kenyon

open TreeEntropy

variable {V E : Type} [Fintype E] [DecidableEq V]

/-- The sum of `g` over the neighbours of `x`, with multiplicity. -/
def nbSum (src tgt : E → V) (g : V → ℝ) (x : V) : ℝ :=
  ∑ e ∈ univ.filter (fun e => src e = x), g (tgt e)
    + ∑ e ∈ univ.filter (fun e => tgt e = x), g (src e)

/-- The operator `D − zA`. -/
def Kop (src tgt : E → V) (z : ℝ) (g : V → ℝ) (x : V) : ℝ :=
  (deg src tgt x : ℝ) * g x - z * nbSum src tgt g x

/-- **Maximum principle.** -/
theorem nonneg_of_Kop_nonneg [Fintype V] {src tgt : E → V} (hdeg : ∀ v, 1 ≤ deg src tgt v)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) {g : V → ℝ} (hK : ∀ x, 0 ≤ Kop src tgt z g x) (x : V) :
    0 ≤ g x := by
  by_contra hx0
  have hx : g x < 0 := not_le.1 hx0
  obtain ⟨x₀, -, hmin⟩ := Finset.exists_min_image univ g ⟨x, Finset.mem_univ x⟩
  have hx₀ : g x₀ < 0 := lt_of_le_of_lt (hmin x (Finset.mem_univ x)) hx
  have hnb : (deg src tgt x₀ : ℝ) * g x₀ ≤ nbSum src tgt g x₀ := by
    have h1 : ((univ.filter fun e => src e = x₀).card : ℝ) * g x₀
        ≤ ∑ e ∈ univ.filter (fun e => src e = x₀), g (tgt e) := by
      have := Finset.card_nsmul_le_sum (univ.filter fun e => src e = x₀) (fun e => g (tgt e))
        (g x₀) fun e _ => hmin (tgt e) (Finset.mem_univ _)
      rwa [nsmul_eq_mul] at this
    have h2 : ((univ.filter fun e => tgt e = x₀).card : ℝ) * g x₀
        ≤ ∑ e ∈ univ.filter (fun e => tgt e = x₀), g (src e) := by
      have := Finset.card_nsmul_le_sum (univ.filter fun e => tgt e = x₀) (fun e => g (src e))
        (g x₀) fun e _ => hmin (src e) (Finset.mem_univ _)
      rwa [nsmul_eq_mul] at this
    unfold nbSum deg
    push_cast
    linarith
  have hd : (1:ℝ) ≤ deg src tgt x₀ := by exact_mod_cast hdeg x₀
  have h0 := hK x₀
  unfold Kop at h0
  nlinarith [mul_nonneg hz0 (sub_nonneg.2 hnb), mul_pos (sub_pos.2 hz1) (neg_pos.2 hx₀)]

/-- A lower bound for the neighbour sum at `x` from dart inequalities into `x`. -/
theorem inSum_mul_le_nbSum (src tgt : E → V) (hp hm : E → ℝ) (g : V → ℝ) (x : V)
    (h1 : ∀ e, tgt e = x → hp e * g x ≤ g (src e))
    (h2 : ∀ e, src e = x → hm e * g x ≤ g (tgt e)) :
    inSum src tgt hp hm x * g x ≤ nbSum src tgt g x := by
  unfold inSum nbSum
  rw [add_mul, Finset.sum_mul, Finset.sum_mul]
  have a1 : ∑ e ∈ univ.filter (fun e => tgt e = x), hp e * g x
      ≤ ∑ e ∈ univ.filter (fun e => tgt e = x), g (src e) :=
    Finset.sum_le_sum fun e he => h1 e (Finset.mem_filter.1 he).2
  have a2 : ∑ e ∈ univ.filter (fun e => src e = x), hm e * g x
      ≤ ∑ e ∈ univ.filter (fun e => src e = x), g (tgt e) :=
    Finset.sum_le_sum fun e he => h2 e (Finset.mem_filter.1 he).2
  linarith

/-- The same without the reverse of the dart `src e → tgt e`. -/
theorem othP_mul_le_nbSum (src tgt : E → V) (hp hm : E → ℝ) (g : V → ℝ) (e : E)
    (h1 : ∀ e', tgt e' = src e → hp e' * g (src e) ≤ g (src e'))
    (h2 : ∀ e', src e' = src e → e' ≠ e → hm e' * g (src e) ≤ g (tgt e')) :
    g (tgt e) + othP src tgt hp hm e * g (src e) ≤ nbSum src tgt g (src e) := by
  classical
  have he : e ∈ univ.filter (fun e' => src e' = src e) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  rw [othP_eq]
  unfold nbSum
  rw [← Finset.add_sum_erase _ (fun e' => g (tgt e')) he, add_mul, Finset.sum_mul, Finset.sum_mul]
  have a1 : ∑ e' ∈ univ.filter (fun e' => tgt e' = src e), hp e' * g (src e)
      ≤ ∑ e' ∈ univ.filter (fun e' => tgt e' = src e), g (src e') :=
    Finset.sum_le_sum fun e' he' => h1 e' (Finset.mem_filter.1 he').2
  have a2 : ∑ e' ∈ (univ.filter (fun e' => src e' = src e)).erase e, hm e' * g (src e)
      ≤ ∑ e' ∈ (univ.filter (fun e' => src e' = src e)).erase e, g (tgt e') :=
    Finset.sum_le_sum fun e' he' =>
      h2 e' (Finset.mem_filter.1 (Finset.mem_of_mem_erase he')).2 (Finset.ne_of_mem_erase he')
  linarith

/-- The same without the reverse of the dart `tgt e → src e`. -/
theorem othM_mul_le_nbSum (src tgt : E → V) (hp hm : E → ℝ) (g : V → ℝ) (e : E)
    (h1 : ∀ e', tgt e' = tgt e → e' ≠ e → hp e' * g (tgt e) ≤ g (src e'))
    (h2 : ∀ e', src e' = tgt e → hm e' * g (tgt e) ≤ g (tgt e')) :
    g (src e) + othM src tgt hp hm e * g (tgt e) ≤ nbSum src tgt g (tgt e) := by
  classical
  have he : e ∈ univ.filter (fun e' => tgt e' = tgt e) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  rw [othM_eq]
  unfold nbSum
  rw [← Finset.add_sum_erase _ (fun e' => g (src e')) he, add_mul, Finset.sum_mul, Finset.sum_mul]
  have a1 : ∑ e' ∈ (univ.filter (fun e' => tgt e' = tgt e)).erase e, hp e' * g (tgt e)
      ≤ ∑ e' ∈ (univ.filter (fun e' => tgt e' = tgt e)).erase e, g (src e') :=
    Finset.sum_le_sum fun e' he' =>
      h1 e' (Finset.mem_filter.1 (Finset.mem_of_mem_erase he')).2 (Finset.ne_of_mem_erase he')
  have a2 : ∑ e' ∈ univ.filter (fun e' => src e' = tgt e), hm e' * g (tgt e)
      ≤ ∑ e' ∈ univ.filter (fun e' => src e' = tgt e), g (tgt e') :=
    Finset.sum_le_sum fun e' he' => h2 e' (Finset.mem_filter.1 he').2
  linarith

section ClassC

variable {src tgt : E → V} (hdeg : ∀ v, 2 ≤ deg src tgt v)
  (hD : ∀ e, ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2))

include hdeg hD in
/-- **Dart inequalities.**  If `g ≥ 0` and `(D − zA) g ≥ 0`, then for every level `s` and every
edge `e`: `g (src e) ≥ h⁽ˢ⁾_{src e → tgt e} · g (tgt e)` and
`g (tgt e) ≥ h⁽ˢ⁾_{tgt e → src e} · g (src e)`. -/
theorem dart_ineq {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) {g : V → ℝ} (g0 : ∀ x, 0 ≤ g x)
    (hK : ∀ x, 0 ≤ Kop src tgt z g x) :
    ∀ s, (∀ e, (lev src tgt z s).1 e * g (tgt e) ≤ g (src e)) ∧
      (∀ e, (lev src tgt z s).2 e * g (src e) ≤ g (tgt e))
  | 0 => ⟨fun e => by simpa [lev] using g0 (src e), fun e => by simpa [lev] using g0 (tgt e)⟩
  | s + 1 => by
      obtain ⟨ih1, ih2⟩ := dart_ineq hz0 hz1 g0 hK s
      have G := good_lev hdeg hD hz0 hz1 s
      refine ⟨fun e => ?_, fun e => ?_⟩
      · have hden := G.denP_pos hdeg hz1 e
        have hnb := othP_mul_le_nbSum src tgt (lev src tgt z s).1 (lev src tgt z s).2 g e
          (fun e' he' => by have := ih1 e'; rwa [he'] at this)
          (fun e' he' _ => by have := ih2 e'; rwa [he'] at this)
        have h0 := hK (src e)
        unfold Kop at h0
        show stepP src tgt z (lev src tgt z s).1 (lev src tgt z s).2 e * g (tgt e) ≤ g (src e)
        unfold stepP
        rw [div_mul_eq_mul_div, div_le_iff₀ hden]
        nlinarith [mul_le_mul_of_nonneg_left hnb hz0]
      · have hden := G.denM_pos hdeg hz1 e
        have hnb := othM_mul_le_nbSum src tgt (lev src tgt z s).1 (lev src tgt z s).2 g e
          (fun e' he' _ => by have := ih1 e'; rwa [he'] at this)
          (fun e' he' => by have := ih2 e'; rwa [he'] at this)
        have h0 := hK (tgt e)
        unfold Kop at h0
        show stepM src tgt z (lev src tgt z s).1 (lev src tgt z s).2 e * g (src e) ≤ g (tgt e)
        unfold stepM
        rw [div_mul_eq_mul_div, div_le_iff₀ hden]
        nlinarith [mul_le_mul_of_nonneg_left hnb hz0]

include hdeg hD in
/-- The dart inequalities for the limit. -/
theorem dart_ineq_sol {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) {g : V → ℝ} (g0 : ∀ x, 0 ≤ g x)
    (hK : ∀ x, 0 ≤ Kop src tgt z g x) :
    (∀ e, solP src tgt z e * g (tgt e) ≤ g (src e)) ∧
      (∀ e, solM src tgt z e * g (src e) ≤ g (tgt e)) :=
  ⟨fun e => le_of_tendsto' ((tendsto_levP hdeg hD hz0 hz1 e).mul_const (g (tgt e)))
      fun s => (dart_ineq hdeg hD hz0 hz1 g0 hK s).1 e,
    fun e => le_of_tendsto' ((tendsto_levM hdeg hD hz0 hz1 e).mul_const (g (src e)))
      fun s => (dart_ineq hdeg hD hz0 hz1 g0 hK s).2 e⟩

include hdeg hD in
/-- **Green comparison.**  If `g ≥ 0` and `(D − zA) g ≥ 0`, then
`((D − zA) g) v ≤ (d_v − z · inSum v) · g v`, where `inSum` is taken for the dart solution. -/
theorem green_sol {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) {g : V → ℝ} (g0 : ∀ x, 0 ≤ g x)
    (hK : ∀ x, 0 ≤ Kop src tgt z g x) (v : V) :
    Kop src tgt z g v
      ≤ ((deg src tgt v : ℝ) - z * inSum src tgt (solP src tgt z) (solM src tgt z) v) * g v := by
  obtain ⟨h1, h2⟩ := dart_ineq_sol hdeg hD hz0 hz1 g0 hK
  have hnb := inSum_mul_le_nbSum src tgt (solP src tgt z) (solM src tgt z) g v
    (fun e he => by have := h1 e; rwa [he] at this)
    (fun e he => by have := h2 e; rwa [he] at this)
  unfold Kop
  nlinarith [mul_le_mul_of_nonneg_left hnb hz0]

end ClassC

end Kenyon
