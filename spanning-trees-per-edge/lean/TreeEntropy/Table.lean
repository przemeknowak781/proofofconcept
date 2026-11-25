/-
  The finite table: values of `f d` at the critical point and at the right ends of the ranges,
  for degrees `2 ≤ d ≤ 119`, as inequalities between natural numbers checked by kernel
  evaluation (`decide +kernel`; no `native_decide`, no extra axioms).
-/
import TreeEntropy.OneVar

namespace TreeEntropy

/-- The natural-number form of `f d (p/s) ≤ (1/16) log (N/D)`. -/
def NatIneq (d p s N D : ℕ) : Prop :=
  (s + p) ^ (9 * d) * p ^ d * D ^ d * (s * d) ^ (16 + 2 * d)
    ≤ N ^ d * (p * d + s) ^ (16 + 2 * d) * s ^ (10 * d)

instance (d p s N D : ℕ) : Decidable (NatIneq d p s N D) := by
  unfold NatIneq; infer_instance

/-- Critical point `1/8`, degrees `3 ≤ d ≤ 9`, constant `(27/8)^4`. -/
theorem tableA1_small : ∀ d : ℕ, d < 10 → 3 ≤ d → NatIneq d 1 8 (27 ^ 4) (8 ^ 4) := by
  decide +kernel

/-- Critical point `1/(d-2)`, degrees `10 ≤ d ≤ 119`, constant `(27/8)^4`. -/
theorem tableA1_large : ∀ d : ℕ, d < 120 → 10 ≤ d → NatIneq d 1 (d - 2) (27 ^ 4) (8 ^ 4) := by
  decide +kernel

/-- Right end `R'_d = (9d-1)/(d(3d+1))`, degrees `3 ≤ d ≤ 119`, constant `(27/8)^4`. -/
theorem tableA2 :
    ∀ d : ℕ, d < 120 → 3 ≤ d → NatIneq d (9 * d - 1) (d * (3 * d + 1)) (27 ^ 4) (8 ^ 4) := by
  decide +kernel

/-- Right end `3/d` with the unrelaxed constant `(27/8)^4`: true for every degree
`3 ≤ d ≤ 119` except `d = 5`. -/
theorem tableA3 : ∀ d : ℕ, d < 120 → 3 ≤ d → d ≠ 5 → NatIneq d 3 d (27 ^ 4) (8 ^ 4) := by
  decide +kernel

/-- Right end `3/d`, degrees `3 ≤ d ≤ 119`, relaxed constant `2 (27/8)^4`. -/
theorem tableB : ∀ d : ℕ, d < 120 → 3 ≤ d → NatIneq d 3 d (2 * 27 ^ 4) (8 ^ 4) := by
  decide +kernel

/-- Degree `2`, critical point `1/8`, tightened constant `(27/8)^4 / 2`. -/
theorem table2 : NatIneq 2 1 8 (27 ^ 4) (2 * 8 ^ 4) := by
  decide +kernel

/-! ### The constants as logarithms -/

theorem log_const_A :
    1 / 16 * Real.log (((27 ^ 4 : ℕ) : ℝ) / ((8 ^ 4 : ℕ) : ℝ)) = 1 / 4 * Real.log (27 / 8) := by
  rw [show (((27 ^ 4 : ℕ) : ℝ) / ((8 ^ 4 : ℕ) : ℝ)) = (27 / 8 : ℝ) ^ 4 by norm_num, Real.log_pow]
  push_cast; ring

theorem log_const_B :
    1 / 16 * Real.log (((2 * 27 ^ 4 : ℕ) : ℝ) / ((8 ^ 4 : ℕ) : ℝ))
      = 1 / 4 * Real.log (27 / 8) + 1 / 16 * Real.log 2 := by
  rw [show (((2 * 27 ^ 4 : ℕ) : ℝ) / ((8 ^ 4 : ℕ) : ℝ)) = 2 * (27 / 8 : ℝ) ^ 4 by norm_num,
    Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  push_cast; ring

theorem log_const_2 :
    1 / 16 * Real.log (((27 ^ 4 : ℕ) : ℝ) / ((2 * 8 ^ 4 : ℕ) : ℝ))
      = 1 / 4 * Real.log (27 / 8) - 1 / 16 * Real.log 2 := by
  rw [show (((27 ^ 4 : ℕ) : ℝ) / ((2 * 8 ^ 4 : ℕ) : ℝ)) = (27 / 8 : ℝ) ^ 4 / 2 by norm_num,
    Real.log_div (by positivity) (by norm_num), Real.log_pow]
  push_cast; ring

/-! ### Bounds for `f d` on the ranges, degrees `2 ≤ d ≤ 119` -/

theorem crit_bound {d : ℕ} (hd3 : 3 ≤ d) (hd : d < 120) {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hend : f (d:ℝ) R ≤ 1 / 4 * Real.log (27 / 8)) : f (d:ℝ) ρ ≤ 1 / 4 * Real.log (27 / 8) := by
  rcases Nat.lt_or_ge d 10 with h10 | h10
  · have hcrit : f (d:ℝ) (1 / 8) ≤ 1 / 4 * Real.log (27 / 8) := by
      have h := f_le_of_nat (d := d) (p := 1) (s := 8) (N := 27 ^ 4) (D := 8 ^ 4) (by omega)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (tableA1_small d h10 hd3)
      rw [log_const_A] at h
      norm_num at h ⊢
      exact h
    have hd3' : (3:ℝ) ≤ d := by exact_mod_cast hd3
    have hd10' : (d:ℝ) ≤ 10 := by exact_mod_cast h10.le
    exact (f_le_max_small hd3' hd10' hρ hρR).trans (max_le hcrit hend)
  · have hcrit : f (d:ℝ) (1 / ((d:ℝ) - 2)) ≤ 1 / 4 * Real.log (27 / 8) := by
      have h := f_le_of_nat (d := d) (p := 1) (s := d - 2) (N := 27 ^ 4) (D := 8 ^ 4) (by omega)
        (by norm_num) (by omega) (by norm_num) (by norm_num) (tableA1_large d hd h10)
      rw [log_const_A, Nat.cast_sub (by omega : 2 ≤ d)] at h
      simpa using h
    have hd10' : (10:ℝ) ≤ d := by exact_mod_cast h10
    exact (f_le_max_large hd10' hρ hρR).trans (max_le hcrit hend)

/-- Degrees `3 ≤ d ≤ 119`, range `(0, R'_d]`: `f d ≤ (1/4) log (27/8)`. -/
theorem caseA_bound {d : ℕ} (hd3 : 3 ≤ d) (hd : d < 120) {ρ : ℝ} (hρ : 0 < ρ)
    (hρR : ρ ≤ (9 * (d:ℝ) - 1) / (d * (3 * d + 1))) : f (d:ℝ) ρ ≤ 1 / 4 * Real.log (27 / 8) := by
  refine crit_bound hd3 hd hρ hρR ?_
  have h := f_le_of_nat (d := d) (p := 9 * d - 1) (s := d * (3 * d + 1)) (N := 27 ^ 4)
    (D := 8 ^ 4) (by omega) (by omega) (by positivity) (by norm_num) (by norm_num)
    (tableA2 d hd hd3)
  rw [log_const_A, Nat.cast_sub (by omega : 1 ≤ 9 * d)] at h
  push_cast at h
  exact h

/-- Degrees `3 ≤ d ≤ 119`, `d ≠ 5`, range `(0, 3/d]`: `f d ≤ (1/4) log (27/8)`. -/
theorem caseA3_bound {d : ℕ} (hd3 : 3 ≤ d) (hd : d < 120) (h5 : d ≠ 5) {ρ : ℝ} (hρ : 0 < ρ)
    (hρR : ρ ≤ 3 / (d:ℝ)) : f (d:ℝ) ρ ≤ 1 / 4 * Real.log (27 / 8) := by
  refine crit_bound hd3 hd hρ hρR ?_
  have h := f_le_of_nat (d := d) (p := 3) (s := d) (N := 27 ^ 4) (D := 8 ^ 4) (by omega)
    (by norm_num) (by omega) (by norm_num) (by norm_num) (tableA3 d hd hd3 h5)
  rw [log_const_A] at h
  push_cast at h
  exact h

/-- Degrees `3 ≤ d ≤ 119`, range `(0, 3/d]`: `f d ≤ (1/4) log (27/8) + (1/16) log 2`. -/
theorem caseB_bound {d : ℕ} (hd3 : 3 ≤ d) (hd : d < 120) {ρ : ℝ} (hρ : 0 < ρ)
    (hρR : ρ ≤ 3 / (d:ℝ)) : f (d:ℝ) ρ ≤ 1 / 4 * Real.log (27 / 8) + 1 / 16 * Real.log 2 := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hend : f (d:ℝ) (3 / (d:ℝ)) ≤ 1 / 4 * Real.log (27 / 8) + 1 / 16 * Real.log 2 := by
    have h := f_le_of_nat (d := d) (p := 3) (s := d) (N := 2 * 27 ^ 4) (D := 8 ^ 4) (by omega)
      (by norm_num) (by omega) (by norm_num) (by norm_num) (tableB d hd hd3)
    rw [log_const_B] at h
    push_cast at h
    exact h
  -- between the critical point and the right end
  rcases Nat.lt_or_ge d 10 with h10 | h10
  · have hcrit : f (d:ℝ) (1 / 8) ≤ 1 / 4 * Real.log (27 / 8) + 1 / 16 * Real.log 2 := by
      have h := f_le_of_nat (d := d) (p := 1) (s := 8) (N := 27 ^ 4) (D := 8 ^ 4) (by omega)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (tableA1_small d h10 hd3)
      rw [log_const_A] at h
      norm_num at h ⊢
      linarith
    have hd3' : (3:ℝ) ≤ d := by exact_mod_cast hd3
    have hd10' : (d:ℝ) ≤ 10 := by exact_mod_cast h10.le
    exact (f_le_max_small hd3' hd10' hρ hρR).trans (max_le hcrit hend)
  · have hcrit : f (d:ℝ) (1 / ((d:ℝ) - 2)) ≤ 1 / 4 * Real.log (27 / 8) + 1 / 16 * Real.log 2 := by
      have h := f_le_of_nat (d := d) (p := 1) (s := d - 2) (N := 27 ^ 4) (D := 8 ^ 4) (by omega)
        (by norm_num) (by omega) (by norm_num) (by norm_num) (tableA1_large d hd h10)
      rw [log_const_A, Nat.cast_sub (by omega : 2 ≤ d)] at h
      have h' : f (d:ℝ) (1 / ((d:ℝ) - 2)) ≤ 1 / 4 * Real.log (27 / 8) := by simpa using h
      linarith
    have hd10' : (10:ℝ) ≤ d := by exact_mod_cast h10
    exact (f_le_max_large hd10' hρ hρR).trans (max_le hcrit hend)

/-- Degree `2`: `f 2 ≤ (1/4) log (27/8) - (1/16) log 2` everywhere. -/
theorem two_bound {ρ : ℝ} (hρ : 0 < ρ) :
    f 2 ρ ≤ 1 / 4 * Real.log (27 / 8) - 1 / 16 * Real.log 2 := by
  have h := f_le_of_nat (d := 2) (p := 1) (s := 8) (N := 27 ^ 4) (D := 2 * 8 ^ 4) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) table2
  rw [log_const_2] at h
  norm_num at h
  exact (f_two_le hρ).trans (by norm_num; exact h)

end TreeEntropy
