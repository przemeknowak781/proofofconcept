/-
  The edge inequality for the tree entropy: summation step.

  Data: a finite multigraph given by `src tgt : E → V` (loops and parallel edges allowed),
  positive reals `x : V → ℝ` and `r : E → ℝ`.  `deg v` counts the edge-ends at `v`, and
  `endSum r v` sums `r` over the edge-ends at `v`.

  `sum_identity`: if `endSum r v = deg v * x v - 1` for every vertex (identity (I2)), then for
  ANY multipliers `c : V → ℝ` the per-edge quantities
      log (1 + r e) - (1/deg u) log x u - (1/deg v) log x v
        - c u (r e - ρ u) - c v (r e - ρ v),        ρ w = x w - 1/deg w,
  sum to `∑ e, log (1 + r e) - ∑ v, log (x v)`.
  `sum_le_of_edge`: hence a bound `≤ L` for every edge gives `≤ |E| * L` for the sum.
-/
import Mathlib

open Finset

namespace TreeEntropy

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- Number of edge-ends at `v` (a loop counts twice). -/
def deg (src tgt : E → V) (v : V) : ℕ :=
  (univ.filter fun e => src e = v).card + (univ.filter fun e => tgt e = v).card

/-- Sum of `r` over the edge-ends at `v`. -/
def endSum (src tgt : E → V) (r : E → ℝ) (v : V) : ℝ :=
  ∑ e ∈ univ.filter (fun e => src e = v), r e + ∑ e ∈ univ.filter (fun e => tgt e = v), r e

/-- Double counting along one end map. -/
theorem sum_fiber (π : E → V) (ψ : V → ℝ) (φ : E → ℝ) :
    ∑ e, ψ (π e) * φ e = ∑ v, ψ v * ∑ e ∈ univ.filter (fun e => π e = v), φ e := by
  rw [← Finset.sum_fiberwise (s := univ) (g := π) (f := fun e => ψ (π e) * φ e)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [(Finset.mem_filter.1 he).2]

theorem sum_fiber_one (π : E → V) (ψ : V → ℝ) :
    ∑ e, ψ (π e) = ∑ v, ψ v * ((univ.filter fun e => π e = v).card : ℝ) := by
  have h := sum_fiber π ψ (fun _ => (1:ℝ))
  simpa using h

/-- **Summation identity** (part (a) of the lemma on the sum of the edge quantities). -/
theorem sum_identity (src tgt : E → V) (x c : V → ℝ) (r : E → ℝ)
    (hdeg : ∀ v, 0 < deg src tgt v)
    (I2 : ∀ v, endSum src tgt r v = deg src tgt v * x v - 1) :
    ∑ e, (Real.log (1 + r e) - 1 / (deg src tgt (src e) : ℝ) * Real.log (x (src e))
        - 1 / (deg src tgt (tgt e) : ℝ) * Real.log (x (tgt e))
        - c (src e) * (r e - (x (src e) - 1 / (deg src tgt (src e) : ℝ)))
        - c (tgt e) * (r e - (x (tgt e) - 1 / (deg src tgt (tgt e) : ℝ))))
      = ∑ e, Real.log (1 + r e) - ∑ v, Real.log (x v) := by
  set A : V → ℝ := fun v => 1 / (deg src tgt v : ℝ) * Real.log (x v)
    - c v * (x v - 1 / (deg src tgt v : ℝ)) with hA
  have hterm : ∀ e, Real.log (1 + r e) - 1 / (deg src tgt (src e) : ℝ) * Real.log (x (src e))
        - 1 / (deg src tgt (tgt e) : ℝ) * Real.log (x (tgt e))
        - c (src e) * (r e - (x (src e) - 1 / (deg src tgt (src e) : ℝ)))
        - c (tgt e) * (r e - (x (tgt e) - 1 / (deg src tgt (tgt e) : ℝ)))
      = Real.log (1 + r e) - A (src e) - A (tgt e) - c (src e) * r e - c (tgt e) * r e := by
    intro e; simp only [hA]; ring
  simp only [hterm, Finset.sum_sub_distrib]
  rw [sum_fiber_one src A, sum_fiber_one tgt A, sum_fiber src c r, sum_fiber tgt c r]
  have hv : ∀ v, A v * ((univ.filter fun e => src e = v).card : ℝ)
      + A v * ((univ.filter fun e => tgt e = v).card : ℝ)
      + c v * ∑ e ∈ univ.filter (fun e => src e = v), r e
      + c v * ∑ e ∈ univ.filter (fun e => tgt e = v), r e = Real.log (x v) := by
    intro v
    have hd : (deg src tgt v : ℝ) ≠ 0 := by exact_mod_cast (hdeg v).ne'
    have hI := I2 v
    simp only [endSum] at hI
    have hcard : ((univ.filter fun e => src e = v).card : ℝ)
        + ((univ.filter fun e => tgt e = v).card : ℝ) = (deg src tgt v : ℝ) := by
      simp only [deg]; push_cast; ring
    have e1 : A v * ((univ.filter fun e => src e = v).card : ℝ)
        + A v * ((univ.filter fun e => tgt e = v).card : ℝ) = A v * (deg src tgt v : ℝ) := by
      rw [← hcard]; ring
    have e2 : c v * ∑ e ∈ univ.filter (fun e => src e = v), r e
        + c v * ∑ e ∈ univ.filter (fun e => tgt e = v), r e
        = c v * ((deg src tgt v : ℝ) * x v - 1) := by
      rw [← hI]; ring
    have e3 : A v * (deg src tgt v : ℝ) + c v * ((deg src tgt v : ℝ) * x v - 1)
        = Real.log (x v) := by
      simp only [hA]; field_simp; ring
    linarith
  have hsum : ∑ v, Real.log (x v)
      = ∑ v, A v * ((univ.filter fun e => src e = v).card : ℝ)
        + ∑ v, A v * ((univ.filter fun e => tgt e = v).card : ℝ)
        + ∑ v, c v * ∑ e ∈ univ.filter (fun e => src e = v), r e
        + ∑ v, c v * ∑ e ∈ univ.filter (fun e => tgt e = v), r e := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => (hv v).symm
  rw [hsum]; ring

/-- From an edge-by-edge bound to the bound on the sum. -/
theorem sum_le_of_edge (src tgt : E → V) (x c : V → ℝ) (r : E → ℝ) (L : ℝ)
    (hdeg : ∀ v, 0 < deg src tgt v)
    (I2 : ∀ v, endSum src tgt r v = deg src tgt v * x v - 1)
    (hedge : ∀ e, Real.log (1 + r e) - 1 / (deg src tgt (src e) : ℝ) * Real.log (x (src e))
        - 1 / (deg src tgt (tgt e) : ℝ) * Real.log (x (tgt e))
        - c (src e) * (r e - (x (src e) - 1 / (deg src tgt (src e) : ℝ)))
        - c (tgt e) * (r e - (x (tgt e) - 1 / (deg src tgt (tgt e) : ℝ))) ≤ L) :
    ∑ e, Real.log (1 + r e) - ∑ v, Real.log (x v) ≤ (Fintype.card E : ℝ) * L := by
  rw [← sum_identity src tgt x c r hdeg I2]
  calc _ ≤ ∑ _e : E, L := Finset.sum_le_sum fun e _ => hedge e
    _ = (Fintype.card E : ℝ) * L := by simp [Finset.sum_const, Finset.card_univ]

end TreeEntropy
