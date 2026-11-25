import Kenyon.Regular
import Kenyon.Lap

/-!
# 4-regular graphs given by an action of four letters

The letters are `0, 1, 2, 3` with the involution `linv` (`0 ↔ 1`, `2 ↔ 3`). An `Act V` is a map
`mv : Fin 4 → V → V` with `mv (linv s) (mv s x) = x`. Its graph has the edges `V × Fin 2`:
the edge `(x, i)` joins `x` to `mv (pos i) x`, `pos 0 = 0`, `pos 1 = 2`. Every degree is `4`.

Counters of walks without backtracking from a vertex `v` (functions, no enumeration of words):
`nu v j x s` counts the reduced words of length `j + 1` with last letter `s` leading from `v`
to `x`, and `uW v j x` those of length `j`.

* `aop_uW_zero`, `aop_uW_one`, `aop_uW_succ` : the recurrences `A u₀ = u₁`,
  `A u₁ = u₂ + 4 u₀`, `A u_{j+2} = u_{j+3} + 3 u_{j+1}`;
* `green_upper` : if no reduced word of length `1, …, k+1` leads from `v` back to `v`, then
  `K(t)⁻¹ v v ≤ (1 + t^(k+2) / (1 − t)) / (4 − 4 t · sVal t)`;
* `trace_inv_mul_Amat_le` : hence `tr (K(t)⁻¹ A) ≤ Wsum t + |V| · 2 t^(k+1) / (1 − t)`.
-/

open Finset Matrix

namespace Kenyon

open TreeEntropy

/-- The inverse letter. -/
def linv : Fin 4 → Fin 4 := ![1, 0, 3, 2]

theorem linv_linv (s : Fin 4) : linv (linv s) = s := by
  fin_cases s <;> rfl

/-- `linv` as a permutation of the letters. -/
def linvEquiv : Fin 4 ≃ Fin 4 := ⟨linv, linv, linv_linv, linv_linv⟩

/-- The positive letters. -/
def pos : Fin 2 → Fin 4 := ![0, 2]

/-- An action of the four letters in which `linv s` undoes `s`. -/
structure Act (V : Type) where
  /-- the action of a letter -/
  mv : Fin 4 → V → V
  cancel : ∀ s x, mv (linv s) (mv s x) = x

namespace Act

variable {V : Type} (A : Act V)

theorem cancel' (s : Fin 4) (x : V) : A.mv s (A.mv (linv s) x) = x := by
  have h := A.cancel (linv s) x
  rwa [linv_linv] at h

theorem mv_inj (s : Fin 4) {x y : V} (h : A.mv s x = A.mv s y) : x = y := by
  have h' := congrArg (A.mv (linv s)) h
  rwa [A.cancel, A.cancel] at h'

theorem mv_eq_iff (s : Fin 4) (x v : V) : A.mv s x = v ↔ x = A.mv (linv s) v := by
  constructor
  · intro h
    rw [← h, A.cancel]
  · intro h
    rw [h, A.cancel']

/-- The source of an edge. -/
def esrc (p : V × Fin 2) : V := p.1

/-- The target of an edge. -/
def etgt (p : V × Fin 2) : V := A.mv (pos p.2) p.1

/-- The adjacency operator. -/
def aop (g : V → ℝ) (x : V) : ℝ := ∑ s, g (A.mv s x)

section Graph

variable [Fintype V] [DecidableEq V]

theorem nbSum_act (g : V → ℝ) (x : V) : nbSum esrc A.etgt g x = A.aop g x := by
  unfold nbSum aop
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type_right,
    Fintype.sum_prod_type_right]
  have h1 : ∀ i : Fin 2, ∑ y : V, (if esrc (y, i) = x then g (A.etgt (y, i)) else 0)
      = g (A.mv (pos i) x) := by
    intro i
    rw [Finset.sum_eq_single x]
    · simp [esrc, etgt]
    · intro y _ hy
      simp [esrc, hy]
    · intro h
      exact absurd (Finset.mem_univ x) h
  have h2 : ∀ i : Fin 2, ∑ y : V, (if A.etgt (y, i) = x then g (esrc (y, i)) else 0)
      = g (A.mv (linv (pos i)) x) := by
    intro i
    rw [Finset.sum_eq_single (A.mv (linv (pos i)) x)]
    · simp [esrc, etgt, A.cancel']
    · intro y _ hy
      have hne : A.etgt (y, i) ≠ x := fun h => hy ((A.mv_eq_iff _ _ _).1 h)
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp only [h1, h2, Fin.sum_univ_two, Fin.sum_univ_four]
  have p0 : pos 0 = 0 := rfl
  have p1 : pos 1 = 2 := rfl
  have l0 : linv 0 = 1 := rfl
  have l2 : linv 2 = 3 := rfl
  rw [p0, p1, l0, l2]
  ring

theorem deg_act (x : V) : deg esrc A.etgt x = 4 := by
  have h := A.nbSum_act (fun _ => (1:ℝ)) x
  unfold nbSum aop at h
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at h
  have h' : ((deg esrc A.etgt x : ℕ) : ℝ) = ((4:ℕ) : ℝ) := by
    unfold deg
    push_cast
    exact h
  exact_mod_cast h'

theorem Kop_act (t : ℝ) (g : V → ℝ) (x : V) :
    Kop esrc A.etgt t g x = 4 * g x - t * A.aop g x := by
  unfold Kop
  rw [A.nbSum_act, A.deg_act]
  norm_num

end Graph

section Counters

variable [DecidableEq V]

/-- `nu v j x s`: the number of reduced words of length `j + 1` with last letter `s` that lead
from `v` to `x`. -/
noncomputable def nu (v : V) : ℕ → V → Fin 4 → ℝ
  | 0, x, s => if x = A.mv s v then 1 else 0
  | j + 1, x, s =>
      (∑ s', nu v j (A.mv (linv s) x) s') - nu v j (A.mv (linv s) x) (linv s)

/-- `uW v j x`: the number of reduced words of length `j` that lead from `v` to `x`. -/
noncomputable def uW (v : V) : ℕ → V → ℝ
  | 0, x => if x = v then 1 else 0
  | j + 1, x => ∑ s, A.nu v j x s

theorem nu_succ_eq (v : V) (j : ℕ) (x : V) (s : Fin 4) :
    A.nu v (j + 1) x s = ∑ s' ∈ univ.erase (linv s), A.nu v j (A.mv (linv s) x) s' := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  rfl

theorem nu_bounds (v : V) : ∀ (j : ℕ) (x : V) (s : Fin 4),
    0 ≤ A.nu v j x s ∧ A.nu v j x s ≤ 3 ^ j
  | 0, x, s => by
      simp only [nu]
      split_ifs <;> norm_num
  | j + 1, x, s => by
      rw [A.nu_succ_eq]
      have hcard : (univ.erase (linv s)).card = 3 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
        simp
      constructor
      · exact Finset.sum_nonneg fun s' _ => (nu_bounds v j _ s').1
      · calc ∑ s' ∈ univ.erase (linv s), A.nu v j (A.mv (linv s) x) s'
            ≤ ∑ _s' ∈ univ.erase (linv s), (3:ℝ) ^ j :=
              Finset.sum_le_sum fun s' _ => (nu_bounds v j _ s').2
          _ = 3 ^ (j + 1) := by
              rw [Finset.sum_const, hcard]
              simp [pow_succ]
              ring

theorem uW_nonneg (v : V) : ∀ (j : ℕ) (x : V), 0 ≤ A.uW v j x
  | 0, x => by
      simp only [uW]
      split_ifs <;> norm_num
  | j + 1, x => Finset.sum_nonneg fun s _ => (A.nu_bounds v j x s).1

theorem uW_succ_le (v : V) (j : ℕ) (x : V) : A.uW v (j + 1) x ≤ 4 * 3 ^ j := by
  calc A.uW v (j + 1) x = ∑ s, A.nu v j x s := rfl
    _ ≤ ∑ _s : Fin 4, (3:ℝ) ^ j := Finset.sum_le_sum fun s _ => (A.nu_bounds v j x s).2
    _ = 4 * 3 ^ j := by simp

theorem aop_uW_zero (v x : V) : A.aop (A.uW v 0) x = A.uW v 1 x := by
  unfold aop
  simp only [uW, nu]
  rw [← Equiv.sum_comp linvEquiv]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h : (A.mv (linvEquiv s) x = v) ↔ (x = A.mv s v) := by
    have h' := A.mv_eq_iff (linv s) x v
    rwa [linv_linv] at h'
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (h.1 h1) h2
  · exact absurd (h.2 h2) h1
  · rfl

/-- The sum over the last letter that would be cancelled. -/
theorem sum_nu_back_zero (v x : V) :
    ∑ σ, A.nu v 0 (A.mv σ x) σ = 4 * A.uW v 0 x := by
  simp only [nu, uW]
  have h : ∀ σ : Fin 4, (if A.mv σ x = A.mv σ v then (1:ℝ) else 0) = if x = v then 1 else 0 := by
    intro σ
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (A.mv_inj σ h1) h2
    · exact absurd (by rw [h2]) h1
    · rfl
  simp [h]

theorem sum_nu_back_succ (v x : V) (i : ℕ) :
    ∑ σ, A.nu v (i + 1) (A.mv σ x) σ = 3 * A.uW v (i + 1) x := by
  have h : ∀ σ : Fin 4, A.nu v (i + 1) (A.mv σ x) σ
      = A.uW v (i + 1) x - A.nu v i x (linv σ) := by
    intro σ
    simp only [nu, uW, A.cancel]
  rw [Finset.sum_congr rfl (fun σ _ => h σ), Finset.sum_sub_distrib]
  have h2 : ∑ σ : Fin 4, A.nu v i x (linv σ) = A.uW v (i + 1) x :=
    Equiv.sum_comp linvEquiv (fun s => A.nu v i x s)
  rw [h2]
  simp
  ring

theorem aop_uW_step (v x : V) (j : ℕ) :
    A.aop (A.uW v (j + 1)) x = A.uW v (j + 2) x + ∑ σ, A.nu v j (A.mv σ x) σ := by
  have h1 : A.uW v (j + 2) x
      = ∑ s, (A.uW v (j + 1) (A.mv (linv s) x) - A.nu v j (A.mv (linv s) x) (linv s)) := by
    simp only [uW, nu]
  have h2 : ∑ s : Fin 4, (A.uW v (j + 1) (A.mv (linv s) x) - A.nu v j (A.mv (linv s) x) (linv s))
      = ∑ σ : Fin 4, (A.uW v (j + 1) (A.mv σ x) - A.nu v j (A.mv σ x) σ) :=
    Equiv.sum_comp linvEquiv (fun σ => A.uW v (j + 1) (A.mv σ x) - A.nu v j (A.mv σ x) σ)
  rw [h1, h2, Finset.sum_sub_distrib]
  unfold aop
  ring

theorem aop_uW_one (v x : V) :
    A.aop (A.uW v 1) x = A.uW v 2 x + 4 * A.uW v 0 x := by
  rw [A.aop_uW_step v x 0, A.sum_nu_back_zero]

theorem aop_uW_succ (v x : V) (i : ℕ) :
    A.aop (A.uW v (i + 2)) x = A.uW v (i + 3) x + 3 * A.uW v (i + 1) x := by
  rw [A.aop_uW_step v x (i + 1), A.sum_nu_back_succ]

/-- The partial sums `∑_{j ≤ J} h^j u_j`. -/
noncomputable def phiJ (v : V) (h : ℝ) : ℕ → V → ℝ
  | 0, x => A.uW v 0 x
  | J + 1, x => phiJ v h J x + h ^ (J + 1) * A.uW v (J + 1) x

theorem aop_phiJ_succ (v : V) (h : ℝ) (J : ℕ) (x : V) :
    A.aop (A.phiJ v h (J + 1)) x
      = A.aop (A.phiJ v h J) x + h ^ (J + 1) * A.aop (A.uW v (J + 1)) x := by
  unfold aop
  simp only [phiJ]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- The partial sum almost solves the equation. -/
theorem phiJ_eq (v : V) {h t : ℝ} (hfix : h * (4 - 3 * t * h) = t) (x : V) :
    ∀ k : ℕ, 4 * A.phiJ v h (k + 1) x - t * A.aop (A.phiJ v h (k + 1)) x
      = (4 - 4 * t * h) * A.uW v 0 x + 3 * t * h ^ (k + 2) * A.uW v (k + 1) x
        - t * h ^ (k + 1) * A.uW v (k + 2) x
  | 0 => by
      rw [A.aop_phiJ_succ]
      have e0 : A.aop (A.phiJ v h 0) x = A.uW v 1 x := A.aop_uW_zero v x
      rw [e0, A.aop_uW_one]
      simp only [phiJ]
      linear_combination (A.uW v 1 x) * hfix
  | k + 1 => by
      have ih := phiJ_eq v hfix x k
      rw [A.aop_phiJ_succ, A.aop_uW_succ]
      have e : A.phiJ v h (k + 1 + 1) x
          = A.phiJ v h (k + 1) x + h ^ (k + 2) * A.uW v (k + 2) x := rfl
      rw [e]
      linear_combination ih + (h ^ (k + 1) * A.uW v (k + 2) x) * hfix

theorem phiJ_self (v : V) (h : ℝ) : ∀ J : ℕ, (∀ j, 1 ≤ j → j ≤ J → A.uW v j v = 0) →
    A.phiJ v h J v = 1
  | 0, _ => by simp [phiJ, uW]
  | J + 1, hg => by
      have ih := phiJ_self v h J (fun j h1 h2 => hg j h1 (by omega))
      simp only [phiJ]
      rw [ih, hg (J + 1) (by omega) le_rfl]
      ring

end Counters

section Green

variable [Fintype V] [DecidableEq V]

/-- **Upper bound for the diagonal of the Green function.** -/
theorem green_upper (v : V) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (k : ℕ)
    (hgirth : ∀ j, 1 ≤ j → j ≤ k + 1 → A.uW v j v = 0) :
    (Kmat esrc A.etgt t)⁻¹ v v ≤ (1 + t ^ (k + 2) / (1 - t)) / (4 - 4 * t * sVal t) := by
  have hreg : ∀ x, deg esrc A.etgt x = 4 := A.deg_act
  have hdeg1 : ∀ x, 1 ≤ deg esrc A.etgt x := fun x => by rw [hreg]; norm_num
  set h := sVal t with hh
  have hfix : h * (4 - 3 * t * h) = t := sVal_fix hreg v ht0 ht1.le
  have h0 : 0 ≤ h := sVal_nonneg ht0 ht1.le
  have h3 : h ≤ t / 3 := sVal_le ht0 ht1.le
  have hP : 2 ≤ 4 - 4 * t * h := by nlinarith [mul_nonneg ht0 h0]
  have hP0 : 0 < 4 - 4 * t * h := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hM := Kmat_posDef hdeg1 ht0 ht1
  have hunit : IsUnit (Kmat esrc A.etgt t).det := hM.det_pos.ne'.isUnit
  set g : V → ℝ := fun u => (Kmat esrc A.etgt t)⁻¹ u v with hg
  have hgcol : g = (Kmat esrc A.etgt t)⁻¹ *ᵥ Pi.single v 1 := by
    ext u
    simp [hg]
  have hKg : ∀ x, Kop esrc A.etgt t g x = if x = v then 1 else 0 := by
    intro x
    rw [← Kmat_mulVec, hgcol, mulVec_mulVec, mul_nonsing_inv _ hunit, one_mulVec,
      Pi.single_apply]
  set β : ℝ := t * h ^ (k + 1) * (4 * 3 ^ (k + 1)) / ((4 - 4 * t * h) * (4 * (1 - t))) with hβ
  set D : V → ℝ := fun x => A.phiJ v h (k + 1) x / (4 - 4 * t * h) + β - g x with hD
  have hKD : ∀ x, 0 ≤ Kop esrc A.etgt t D x := by
    intro x
    have e1 : Kop esrc A.etgt t D x
        = (4 * A.phiJ v h (k + 1) x - t * A.aop (A.phiJ v h (k + 1)) x) / (4 - 4 * t * h)
          + 4 * (1 - t) * β - Kop esrc A.etgt t g x := by
      rw [A.Kop_act, A.Kop_act]
      unfold aop
      simp only [hD, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div]
      push_cast
      ring
    have e2 : 4 * (1 - t) * β = t * h ^ (k + 1) * (4 * 3 ^ (k + 1)) / (4 - 4 * t * h) := by
      rw [hβ]
      field_simp
    have e3 : A.uW v 0 x = if x = v then 1 else 0 := rfl
    rw [e1, A.phiJ_eq v hfix x k, e2, hKg x, ← e3]
    have hu1 := A.uW_nonneg v (k + 1) x
    have hu2 := A.uW_succ_le v (k + 1) x
    have e4 : ((4 - 4 * t * h) * A.uW v 0 x + 3 * t * h ^ (k + 2) * A.uW v (k + 1) x
          - t * h ^ (k + 1) * A.uW v (k + 2) x) / (4 - 4 * t * h)
          + t * h ^ (k + 1) * (4 * 3 ^ (k + 1)) / (4 - 4 * t * h) - A.uW v 0 x
        = (3 * t * h ^ (k + 2) * A.uW v (k + 1) x
          + t * h ^ (k + 1) * (4 * 3 ^ (k + 1) - A.uW v (k + 2) x)) / (4 - 4 * t * h) := by
      have hi : (4 - 4 * t * h) * (4 - 4 * t * h)⁻¹ = 1 := mul_inv_cancel₀ hP0.ne'
      simp only [div_eq_mul_inv]
      linear_combination (A.uW v 0 x) * hi
    rw [e4]
    apply div_nonneg _ hP0.le
    have a1 : 0 ≤ 3 * t * h ^ (k + 2) * A.uW v (k + 1) x := by positivity
    have a2 : 0 ≤ t * h ^ (k + 1) * (4 * 3 ^ (k + 1) - A.uW v (k + 2) x) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  have hDv := nonneg_of_Kop_nonneg hdeg1 ht0 ht1 hKD v
  simp only [hD] at hDv
  rw [A.phiJ_self v h (k + 1) hgirth] at hDv
  have hβle : β ≤ t ^ (k + 2) / (1 - t) / (4 - 4 * t * h) := by
    have e5 : β = t * (3 * h) ^ (k + 1) / (1 - t) / (4 - 4 * t * h) := by
      rw [hβ, mul_pow]
      field_simp
    rw [e5]
    apply div_le_div_of_nonneg_right _ hP0.le
    apply div_le_div_of_nonneg_right _ h1t.le
    have h3h : (3 * h) ^ (k + 1) ≤ t ^ (k + 1) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    calc t * (3 * h) ^ (k + 1) ≤ t * t ^ (k + 1) := mul_le_mul_of_nonneg_left h3h ht0
      _ = t ^ (k + 2) := by ring
  have e6 : (1 + t ^ (k + 2) / (1 - t)) / (4 - 4 * t * h)
      = 1 / (4 - 4 * t * h) + t ^ (k + 2) / (1 - t) / (4 - 4 * t * h) := by ring
  rw [e6]
  linarith

/-- **Upper bound for the trace.** -/
theorem trace_inv_mul_Amat_le [Nonempty V] {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (k : ℕ)
    (hgirth : ∀ v j, 1 ≤ j → j ≤ k + 1 → A.uW v j v = 0) :
    ((Kmat esrc A.etgt t)⁻¹ * Amat esrc A.etgt).trace
      ≤ Wsum esrc A.etgt t + (Fintype.card V : ℝ) * (2 * t ^ (k + 1) / (1 - t)) := by
  have hreg : ∀ x, deg esrc A.etgt x = 4 := A.deg_act
  have hdeg1 : ∀ x, 1 ≤ deg esrc A.etgt x := fun x => by rw [hreg]; norm_num
  obtain ⟨v₀⟩ := ‹Nonempty V›
  set h := sVal t with hh
  have hfix : h * (4 - 3 * t * h) = t := sVal_fix hreg v₀ ht0.le ht1.le
  have h0 : 0 ≤ h := sVal_nonneg ht0.le ht1.le
  have h3 : h ≤ t / 3 := sVal_le ht0.le ht1.le
  have hP : 2 ≤ 4 - 4 * t * h := by nlinarith [mul_nonneg ht0.le h0]
  have hP0 : 0 < 4 - 4 * t * h := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hM := Kmat_posDef hdeg1 ht0.le ht1
  have hunit : IsUnit (Kmat esrc A.etgt t).det := hM.det_pos.ne'.isUnit
  rw [trace_mul_comm, Wsum_reg hreg]
  have hterm : ∀ v, (Amat esrc A.etgt * (Kmat esrc A.etgt t)⁻¹).diag v
      ≤ 4 * h / (4 - 4 * t * h) + 2 * t ^ (k + 1) / (1 - t) := by
    intro v
    set g : V → ℝ := fun u => (Kmat esrc A.etgt t)⁻¹ u v with hg
    have hgA : (Amat esrc A.etgt * (Kmat esrc A.etgt t)⁻¹).diag v = nbSum esrc A.etgt g v := by
      rw [← Amat_mulVec]
      simp [Matrix.mul_apply, mulVec, dotProduct, hg]
    have hgcol : g = (Kmat esrc A.etgt t)⁻¹ *ᵥ Pi.single v 1 := by
      ext u
      simp [hg]
    have hKg : Kop esrc A.etgt t g v = 1 := by
      rw [← Kmat_mulVec, hgcol, mulVec_mulVec, mul_nonsing_inv _ hunit, one_mulVec,
        Pi.single_apply]
      simp
    unfold Kop at hKg
    rw [hreg] at hKg
    push_cast at hKg
    have hup := A.green_upper v ht0.le ht1 k (hgirth v)
    rw [hgA]
    -- t * nbSum = 4 g v - 1
    have e1 : nbSum esrc A.etgt g v = (4 * g v - 1) / t := by
      rw [eq_div_iff ht0.ne']
      linarith
    rw [e1, div_le_iff₀ ht0]
    have hgv : g v ≤ (1 + t ^ (k + 2) / (1 - t)) / (4 - 4 * t * h) := hup
    have e2 : 4 * ((1 + t ^ (k + 2) / (1 - t)) / (4 - 4 * t * h)) - 1
        = (4 * h / (4 - 4 * t * h)) * t + 4 * (t ^ (k + 1) / (1 - t)) / (4 - 4 * t * h) * t := by
      have hi : (4 - 4 * t * h) * (4 - 4 * t * h)⁻¹ = 1 := mul_inv_cancel₀ hP0.ne'
      simp only [div_eq_mul_inv]
      linear_combination hi
    have e3 : 4 * (t ^ (k + 1) / (1 - t)) / (4 - 4 * t * h) ≤ 2 * t ^ (k + 1) / (1 - t) := by
      rw [div_le_iff₀ hP0]
      have hq : 0 ≤ t ^ (k + 1) / (1 - t) := by positivity
      have : 2 * t ^ (k + 1) / (1 - t) = 2 * (t ^ (k + 1) / (1 - t)) := by ring
      rw [this]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right e3 ht0.le]
  calc (Amat esrc A.etgt * (Kmat esrc A.etgt t)⁻¹).trace
      = ∑ v, (Amat esrc A.etgt * (Kmat esrc A.etgt t)⁻¹).diag v := rfl
    _ ≤ ∑ _v : V, (4 * h / (4 - 4 * t * h) + 2 * t ^ (k + 1) / (1 - t)) :=
        Finset.sum_le_sum fun v _ => hterm v
    _ = (Fintype.card V : ℝ) * (4 * sVal t / (4 - 4 * t * sVal t))
        + (Fintype.card V : ℝ) * (2 * t ^ (k + 1) / (1 - t)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Green

end Act

end Kenyon
