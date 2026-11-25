/-
  One-variable analysis for the edge inequality.

  `g r = (9/16) log (1 + r) + (1/16) log r` is concave; `gp` is its derivative.
  `f d r = g r - (1/d + 1/8) log (r + 1/d)`.

  * `edge_le_f`      the per-edge quantity is at most `f a ρ_u + f b ρ_v`;
  * `hasDerivAt_f`, `f_deriv_eq`: `f d` has derivative
        (8 r - 1) ((d - 2) r - 1) / (16 d r (1 + r) (r + 1/d));
  * `f_le_max`       on `(0, R]` the function `f d` is at most `max (f d p) (f d R)`, where `p` is
                     the smaller of the two critical points `1/8`, `1/(d - 2)`;
  * `f_four_eighth`  `f 4 (1/8) = (1/4) log (27/8)` exactly;
  * `f_le_of_nat`    a value `f d (p/s) ≤ (1/16) log (N/D)` follows from an inequality between
                     natural numbers.
-/
import TreeEntropy.Sum

open Finset

namespace TreeEntropy

/-- `f_d(r) = (9/16) log (1 + r) + (1/16) log r - (1/d + 1/8) log (r + 1/d)`. -/
noncomputable def f (d r : ℝ) : ℝ :=
  9 / 16 * Real.log (1 + r) + 1 / 16 * Real.log r - (1 / d + 1 / 8) * Real.log (r + 1 / d)

/-- The derivative of `g r = (9/16) log (1 + r) + (1/16) log r`. -/
noncomputable def gp (ρ : ℝ) : ℝ := 9 / 16 / (1 + ρ) + 1 / 16 / ρ

theorem gp_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < gp ρ := by
  unfold gp; positivity

/-- Tangent-line inequality for the logarithm. -/
theorem log_le_tangent {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Real.log t ≤ Real.log s + (t - s) / s := by
  have h := Real.log_le_sub_one_of_pos (div_pos ht hs)
  rw [Real.log_div ht.ne' hs.ne'] at h
  have : t / s - 1 = (t - s) / s := by field_simp
  linarith

/-- Concavity of `g`, as a tangent-line inequality. -/
theorem g_le_tangent {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) :
    9 / 16 * Real.log (1 + r) + 1 / 16 * Real.log r
      ≤ 9 / 16 * Real.log (1 + ρ) + 1 / 16 * Real.log ρ + gp ρ * (r - ρ) := by
  have h1 := log_le_tangent (s := 1 + ρ) (t := 1 + r) (by linarith) (by linarith)
  have h2 := log_le_tangent hρ hr
  have e1 : (1 + r - (1 + ρ)) / (1 + ρ) = (r - ρ) / (1 + ρ) := by ring
  rw [e1] at h1
  have e2 : gp ρ * (r - ρ) = 9 / 16 * ((r - ρ) / (1 + ρ)) + 1 / 16 * ((r - ρ) / ρ) := by
    unfold gp; ring
  rw [e2]; nlinarith [h1, h2]

/-- **Bound by the one-variable functions** (part (b) of the lemma on the sum of the edge
quantities).  For an edge with end degrees `a, b`, end values `xu, xv` and edge value `r`
related by `r (1 + r) = xu xv`, the per-edge quantity is at most `f a ρ_u + f b ρ_v`. -/
theorem edge_le_f {a b xu xv r : ℝ} (hr : 0 < r)
    (hρu : 0 < xu - 1 / a) (hρv : 0 < xv - 1 / b) (hxu : 0 < xu) (hxv : 0 < xv)
    (I1 : r * (1 + r) = xu * xv) :
    Real.log (1 + r) - 1 / a * Real.log xu - 1 / b * Real.log xv
      - gp (xu - 1 / a) * (r - (xu - 1 / a)) - gp (xv - 1 / b) * (r - (xv - 1 / b))
      ≤ f a (xu - 1 / a) + f b (xv - 1 / b) := by
  have hlog : Real.log r + Real.log (1 + r) = Real.log xu + Real.log xv := by
    rw [← Real.log_mul hr.ne' (by linarith : (1:ℝ) + r ≠ 0), I1, Real.log_mul hxu.ne' hxv.ne']
  have t1 := g_le_tangent hρu hr
  have t2 := g_le_tangent hρv hr
  simp only [f, sub_add_cancel]
  nlinarith [t1, t2, hlog]

/-! ### The derivative of `f d` -/

theorem hasDerivAt_f {d r : ℝ} (hd : 0 < d) (hr : 0 < r) :
    HasDerivAt (f d)
      (9 / 16 * (1 / (1 + r)) + 1 / 16 * (1 / r) - (1 / d + 1 / 8) * (1 / (r + 1 / d))) r := by
  have h1 : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + r)) r :=
    ((hasDerivAt_id r).const_add 1).log (by show (1:ℝ) + r ≠ 0; positivity)
  have h2 : HasDerivAt (fun y : ℝ => Real.log y) (1 / r) r := by
    simpa using Real.hasDerivAt_log hr.ne'
  have h3 : HasDerivAt (fun y : ℝ => Real.log (y + 1 / d)) (1 / (r + 1 / d)) r :=
    ((hasDerivAt_id r).add_const (1 / d)).log (by show r + 1 / d ≠ 0; positivity)
  exact ((h1.const_mul (9 / 16)).add (h2.const_mul (1 / 16))).sub (h3.const_mul (1 / d + 1 / 8))

theorem f_deriv_eq {d r : ℝ} (hd : 0 < d) (hr : 0 < r) :
    9 / 16 * (1 / (1 + r)) + 1 / 16 * (1 / r) - (1 / d + 1 / 8) * (1 / (r + 1 / d))
      = (8 * r - 1) * ((d - 2) * r - 1) / (16 * d * r * (1 + r) * (r + 1 / d)) := by
  have h1 : (1:ℝ) + r ≠ 0 := by positivity
  have h2 : r + 1 / d ≠ 0 := by positivity
  field_simp
  ring

/-- `f d` is nondecreasing between `α ≤ β` when `(8 r - 1) ((d - 2) r - 1) ≥ 0` in between. -/
theorem f_mono {d α β : ℝ} (hd : 0 < d) (hα : 0 < α) (hαβ : α ≤ β)
    (hQ : ∀ r, α < r → r < β → 0 ≤ (8 * r - 1) * ((d - 2) * r - 1)) : f d α ≤ f d β := by
  have hmono : MonotoneOn (f d) (Set.Icc α β) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc α β) ?_ ?_ ?_
    · intro r hr
      exact (hasDerivAt_f hd (lt_of_lt_of_le hα hr.1)).continuousAt.continuousWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      exact (hasDerivAt_f hd (lt_trans hα hr.1)).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      have hr0 : 0 < r := lt_trans hα hr.1
      rw [(hasDerivAt_f hd hr0).deriv, f_deriv_eq hd hr0]
      exact div_nonneg (hQ r hr.1 hr.2) (by positivity)
  exact hmono ⟨le_rfl, hαβ⟩ ⟨hαβ, le_rfl⟩ hαβ

/-- `f d` is nonincreasing between `α ≤ β` when `(8 r - 1) ((d - 2) r - 1) ≤ 0` in between. -/
theorem f_anti {d α β : ℝ} (hd : 0 < d) (hα : 0 < α) (hαβ : α ≤ β)
    (hQ : ∀ r, α < r → r < β → (8 * r - 1) * ((d - 2) * r - 1) ≤ 0) : f d β ≤ f d α := by
  have hanti : AntitoneOn (f d) (Set.Icc α β) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc α β) ?_ ?_ ?_
    · intro r hr
      exact (hasDerivAt_f hd (lt_of_lt_of_le hα hr.1)).continuousAt.continuousWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      exact (hasDerivAt_f hd (lt_trans hα hr.1)).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      have hr0 : 0 < r := lt_trans hα hr.1
      rw [(hasDerivAt_f hd hr0).deriv, f_deriv_eq hd hr0]
      exact div_nonpos_of_nonpos_of_nonneg (hQ r hr.1 hr.2) (by positivity)
  exact hanti ⟨le_rfl, hαβ⟩ ⟨hαβ, le_rfl⟩ hαβ

/-- If the sign pattern of the derivative is `+, -, +` with changes at `p ≤ P`, then on `(0, R]`
the function is at most `max (f d p) (f d R)`. -/
theorem f_le_max_of_signs {d p P R ρ : ℝ} (hd : 0 < d) (hp : 0 < p)
    (hQ1 : ∀ r, 0 < r → r < p → 0 ≤ (8 * r - 1) * ((d - 2) * r - 1))
    (hQ2 : ∀ r, p < r → r < P → (8 * r - 1) * ((d - 2) * r - 1) ≤ 0)
    (hQ3 : ∀ r, P < r → 0 ≤ (8 * r - 1) * ((d - 2) * r - 1))
    (hρ : 0 < ρ) (hρR : ρ ≤ R) : f d ρ ≤ max (f d p) (f d R) := by
  rcases le_or_gt ρ p with h1 | h1
  · exact le_max_of_le_left (f_mono hd hρ h1 fun r hr1 hr2 => hQ1 r (lt_trans hρ hr1) hr2)
  · rcases le_or_gt ρ P with h2 | h2
    · exact le_max_of_le_left
        (f_anti hd hp h1.le fun r hr1 hr2 => hQ2 r hr1 (lt_of_lt_of_le hr2 h2))
    · exact le_max_of_le_right
        (f_mono hd hρ hρR fun r hr1 _ => hQ3 r (lt_trans h2 hr1))

/-- Degrees `3 ≤ d ≤ 10`: the smaller critical point is `1/8`. -/
theorem f_le_max_small {d R ρ : ℝ} (hd3 : 3 ≤ d) (hd10 : d ≤ 10) (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    f d ρ ≤ max (f d (1 / 8)) (f d R) := by
  have hd2 : 0 < d - 2 := by linarith
  refine f_le_max_of_signs (P := 1 / (d - 2)) (by linarith) (by norm_num) ?_ ?_ ?_ hρ hρR
  · intro r hr0 hr
    have h1 : 8 * r - 1 ≤ 0 := by linarith
    have h2 : (d - 2) * r - 1 ≤ 0 := by nlinarith
    exact mul_nonneg_of_nonpos_of_nonpos h1 h2
  · intro r hr1 hr2
    have h1 : 0 ≤ 8 * r - 1 := by linarith
    have h2 : (d - 2) * r - 1 ≤ 0 := by
      rw [lt_div_iff₀ hd2] at hr2; linarith
    exact mul_nonpos_of_nonneg_of_nonpos h1 h2
  · intro r hr
    rw [div_lt_iff₀ hd2] at hr
    have h1 : 0 ≤ 8 * r - 1 := by nlinarith
    have h2 : 0 ≤ (d - 2) * r - 1 := by linarith
    exact mul_nonneg h1 h2

/-- Degrees `d ≥ 10`: the smaller critical point is `1/(d - 2)`. -/
theorem f_le_max_large {d R ρ : ℝ} (hd10 : 10 ≤ d) (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    f d ρ ≤ max (f d (1 / (d - 2))) (f d R) := by
  have hd2 : 0 < d - 2 := by linarith
  refine f_le_max_of_signs (P := 1 / 8) (by linarith) (by positivity) ?_ ?_ ?_ hρ hρR
  · intro r hr0 hr
    rw [lt_div_iff₀ hd2] at hr
    have h1 : 8 * r - 1 ≤ 0 := by nlinarith
    have h2 : (d - 2) * r - 1 ≤ 0 := by linarith
    exact mul_nonneg_of_nonpos_of_nonpos h1 h2
  · intro r hr1 hr2
    rw [div_lt_iff₀ hd2] at hr1
    have h1 : 8 * r - 1 ≤ 0 := by linarith
    have h2 : 0 ≤ (d - 2) * r - 1 := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg h1 h2
  · intro r hr
    have h1 : 0 ≤ 8 * r - 1 := by linarith
    have h2 : 0 ≤ (d - 2) * r - 1 := by nlinarith
    exact mul_nonneg h1 h2

/-- Degree `2`: `f 2` is largest at `1/8`. -/
theorem f_two_le {ρ : ℝ} (hρ : 0 < ρ) : f 2 ρ ≤ f 2 (1 / 8) := by
  rcases le_or_gt ρ (1 / 8) with h | h
  · refine f_mono (by norm_num) hρ h fun r _ hr2 => ?_
    nlinarith
  · refine f_anti (by norm_num) (by norm_num) h.le fun r hr1 _ => ?_
    nlinarith

/-! ### Exact value at the extremal point -/

theorem f_four_eighth : f 4 (1 / 8) = 1 / 4 * Real.log (27 / 8) := by
  have h3 : (0:ℝ) < 3 := by norm_num
  have h2 : (0:ℝ) < 2 := by norm_num
  have e1 : Real.log (1 + 1 / 8 : ℝ) = 2 * Real.log 3 - 3 * Real.log 2 := by
    rw [show (1 + 1 / 8 : ℝ) = 3 ^ 2 / 2 ^ 3 by norm_num, Real.log_div (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]; push_cast; ring
  have e2 : Real.log (1 / 8 : ℝ) = -(3 * Real.log 2) := by
    rw [show (1 / 8 : ℝ) = (2 ^ 3)⁻¹ by norm_num, Real.log_inv, Real.log_pow]; push_cast; ring
  have e3 : Real.log (1 / 8 + 1 / 4 : ℝ) = Real.log 3 - 3 * Real.log 2 := by
    rw [show (1 / 8 + 1 / 4 : ℝ) = 3 / 2 ^ 3 by norm_num, Real.log_div (by positivity) (by positivity),
      Real.log_pow]; push_cast; ring
  have e4 : Real.log (27 / 8 : ℝ) = 3 * Real.log 3 - 3 * Real.log 2 := by
    rw [show (27 / 8 : ℝ) = 3 ^ 3 / 2 ^ 3 by norm_num, Real.log_div (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]; push_cast; ring
  simp only [f]
  rw [e1, e2, e3, e4]; ring

/-! ### From natural numbers to values of `f` -/

/-- If `(s+p)^(9d) p^d D^d (s d)^(16+2d) ≤ N^d (p d + s)^(16+2d) s^(10d)` in `ℕ`, then
`f d (p/s) ≤ (1/16) log (N/D)`. -/
theorem f_le_of_nat {d p s N D : ℕ} (hd : 0 < d) (hp : 0 < p) (hs : 0 < s) (hN : 0 < N)
    (hD : 0 < D)
    (h : (s + p) ^ (9 * d) * p ^ d * D ^ d * (s * d) ^ (16 + 2 * d)
      ≤ N ^ d * (p * d + s) ^ (16 + 2 * d) * s ^ (10 * d)) :
    f (d : ℝ) ((p : ℝ) / s) ≤ 1 / 16 * Real.log ((N : ℝ) / D) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have hcast : ((s:ℝ) + p) ^ (9 * d) * (p:ℝ) ^ d * (D:ℝ) ^ d * ((s:ℝ) * d) ^ (16 + 2 * d)
      ≤ (N:ℝ) ^ d * ((p:ℝ) * d + s) ^ (16 + 2 * d) * (s:ℝ) ^ (10 * d) := by
    exact_mod_cast h
  have hlog := Real.log_le_log (by positivity) hcast
  have hsp : (0:ℝ) < (s:ℝ) + p := by positivity
  have hpds : (0:ℝ) < (p:ℝ) * d + s := by positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_mul hsR.ne' hdR.ne'] at hlog
  push_cast at hlog
  -- the three logarithms in `f`
  have e1 : Real.log (1 + (p:ℝ) / s) = Real.log ((s:ℝ) + p) - Real.log s := by
    rw [show (1 + (p:ℝ) / s) = ((s:ℝ) + p) / s by field_simp, Real.log_div hsp.ne' hsR.ne']
  have e2 : Real.log ((p:ℝ) / s) = Real.log p - Real.log s := Real.log_div hpR.ne' hsR.ne'
  have e3 : Real.log ((p:ℝ) / s + 1 / d) = Real.log ((p:ℝ) * d + s) - Real.log s - Real.log d := by
    rw [show ((p:ℝ) / s + 1 / d) = ((p:ℝ) * d + s) / (s * d) by field_simp,
      Real.log_div hpds.ne' (by positivity), Real.log_mul hsR.ne' hdR.ne']; ring
  have e4 : Real.log ((N:ℝ) / D) = Real.log N - Real.log D := Real.log_div hNR.ne' hDR.ne'
  simp only [f]
  rw [e1, e2, e3, e4]
  -- multiply the goal by `16 d`
  have key : 16 * (d:ℝ) * (9 / 16 * (Real.log ((s:ℝ) + p) - Real.log s)
      + 1 / 16 * (Real.log p - Real.log s)
      - (1 / (d:ℝ) + 1 / 8) * (Real.log ((p:ℝ) * d + s) - Real.log s - Real.log d))
      ≤ 16 * (d:ℝ) * (1 / 16 * (Real.log N - Real.log D)) := by
    have hexp : 16 * (d:ℝ) * (9 / 16 * (Real.log ((s:ℝ) + p) - Real.log s)
        + 1 / 16 * (Real.log p - Real.log s)
        - (1 / (d:ℝ) + 1 / 8) * (Real.log ((p:ℝ) * d + s) - Real.log s - Real.log d))
        = 9 * d * Real.log ((s:ℝ) + p) + d * Real.log p + (16 + 2 * d) * (Real.log s + Real.log d)
          - (16 + 2 * d) * Real.log ((p:ℝ) * d + s) - 10 * d * Real.log s := by
      field_simp; ring
    rw [hexp]; nlinarith [hlog]
  exact le_of_mul_le_mul_left key (by positivity)

end TreeEntropy
