/-
  Large degrees: an edge with an end of degree at least 120.

  Here the table is replaced by a direct estimate.  Dropping the terms `- gp ρ * r ≤ 0` in the
  per-edge quantity leaves
      log (1 + r) + H a ρ_u + H b ρ_v,     H d s = -(1/d) log (1/d + s) + (9/16) s/(1+s) + 1/16.
  * `H_le_univ`-type bounds: `H a s ≤ (log 3)/3 + 1/16` on the range of every degree `a ≥ 2`;
  * `H_le_big`:   `H b s ≤ (log b)/b + 27/(16 b) + 1/16` on `(0, 3/b]`;
  * `r ≤ x_u x_v ≤ (3/2)(4/b) = 6/b`.
  For `b ≥ 120` the three contributions add up to less than `(1/2) log (27/8)`.
-/
import TreeEntropy.OneVar

namespace TreeEntropy

/-- `H_d(s) = -(1/d) log (1/d + s) + (9/16) s/(1+s) + 1/16`. -/
noncomputable def H (d s : ℝ) : ℝ :=
  -(1 / d) * Real.log (1 / d + s) + 9 / 16 * (s / (1 + s)) + 1 / 16

theorem gp_mul_self {ρ : ℝ} (hρ : 0 < ρ) : gp ρ * ρ = 9 / 16 * (ρ / (1 + ρ)) + 1 / 16 := by
  unfold gp; field_simp

/-- The per-edge quantity is at most `r + H a ρ_u + H b ρ_v`. -/
theorem edge_le_H {a b xu xv r : ℝ} (hr : 0 < r)
    (hρu : 0 < xu - 1 / a) (hρv : 0 < xv - 1 / b) :
    Real.log (1 + r) - 1 / a * Real.log xu - 1 / b * Real.log xv
      - gp (xu - 1 / a) * (r - (xu - 1 / a)) - gp (xv - 1 / b) * (r - (xv - 1 / b))
      ≤ r + H a (xu - 1 / a) + H b (xv - 1 / b) := by
  have h1 : Real.log (1 + r) ≤ r := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + r)
    linarith
  have gu := mul_pos (gp_pos hρu) hr
  have gv := mul_pos (gp_pos hρv) hr
  have eu := gp_mul_self hρu
  have ev := gp_mul_self hρv
  have hu : 1 / a + (xu - 1 / a) = xu := by ring
  have hv : 1 / b + (xv - 1 / b) = xv := by ring
  simp only [H, hu, hv]
  nlinarith [gu, gv, eu, ev, h1]

/-! ### Elementary facts about logarithms -/

theorem log_div_antitone {c a : ℝ} (hc : 3 ≤ c) (hca : c ≤ a) :
    Real.log a / a ≤ Real.log c / c := by
  have he : Real.exp 1 ≤ c := by
    have := Real.exp_one_lt_d9
    norm_num at this
    linarith
  exact Real.log_div_self_antitoneOn (Set.mem_Ici.2 he) (Set.mem_Ici.2 (he.trans hca)) hca

theorem log_two_half_le : Real.log 2 / 2 ≤ Real.log 3 / 3 := by
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9:ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have : Real.log 8 ≤ Real.log 9 := Real.log_le_log (by norm_num) (by norm_num)
  linarith

/-- `log 3 ≥ log 2 + 2/5`, from `log (1 + y) ≥ 2y/(y + 2)` at `y = 1/2`. -/
theorem log_three_ge : Real.log 2 + 2 / 5 ≤ Real.log 3 := by
  have h := Real.le_log_one_add_of_nonneg (x := 1 / 2) (by norm_num)
  have e : Real.log (1 + 1 / 2) = Real.log 3 - Real.log 2 := by
    rw [show (1:ℝ) + 1 / 2 = 3 / 2 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [e] at h
  norm_num at h
  linarith

theorem log_two_lt : Real.log 2 < 7 / 10 := by
  have := Real.log_two_lt_d9
  norm_num at this
  linarith

/-! ### Bounds for `H` -/

/-- `log (1 + y) ≥ 2y/(y + 2)` turns `H a s` into `(log a)/a` plus a rational function. -/
theorem H_le_aux {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    H a s ≤ Real.log a / a
      + s * ((9 * a - 32) * s - 14) / (16 * (2 + a * s) * (1 + s)) + 1 / 16 := by
  have has : 0 < a * s := mul_pos ha hs
  have hlog : Real.log (1 / a + s) = Real.log (1 + a * s) - Real.log a := by
    rw [show 1 / a + s = (1 + a * s) / a by field_simp, Real.log_div (by positivity) ha.ne']
  have hl := Real.le_log_one_add_of_nonneg has.le
  have key : -(1 / a) * (2 * (a * s) / (a * s + 2)) + 9 / 16 * (s / (1 + s))
      = s * ((9 * a - 32) * s - 14) / (16 * (2 + a * s) * (1 + s)) := by
    field_simp; ring
  have hinv : 0 < 1 / a := by positivity
  have hm := mul_le_mul_of_nonneg_left hl hinv.le
  have e : Real.log a / a = 1 / a * Real.log a := by ring
  unfold H
  rw [hlog, e]
  nlinarith [hm, key]

theorem H_two_le {s : ℝ} (hs : 0 < s) : H 2 s ≤ Real.log 3 / 3 + 1 / 16 := by
  have h := H_le_aux (a := 2) (by norm_num) hs
  have hextra : s * ((9 * 2 - 32) * s - 14) / (16 * (2 + 2 * s) * (1 + s)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [mul_pos hs hs]
    · positivity
  linarith [log_two_half_le]

theorem mul_le_three {a s : ℝ} (ha : 0 < a) (hsR : s ≤ 3 / a) : a * s ≤ 3 := by
  have := mul_le_mul_of_nonneg_left hsR ha.le
  rwa [mul_div_cancel₀ _ ha.ne'] at this

/-- Degrees `3 ≤ a ≤ 7`: the rational part is nonpositive on `(0, 3/a]`. -/
theorem H_le_small {a s : ℝ} (ha3 : 3 ≤ a) (ha7 : a ≤ 7) (hs : 0 < s) (hsR : s ≤ 3 / a) :
    H a s ≤ Real.log 3 / 3 + 1 / 16 := by
  have ha : 0 < a := by linarith
  have h := H_le_aux ha hs
  have has : a * s ≤ 3 := mul_le_three ha hsR
  have hbr : (9 * a - 32) * s - 14 ≤ 0 := by
    rcases le_total (9 * a - 32) 0 with h0 | h0
    · nlinarith [mul_nonneg (neg_nonneg.2 h0) hs.le]
    · have h1 : a * ((9 * a - 32) * s - 14) ≤ 0 := by
        nlinarith [mul_nonneg h0 (sub_nonneg.2 has)]
      by_contra hc
      rw [not_le] at hc
      nlinarith [mul_pos ha hc]
  have hextra : s * ((9 * a - 32) * s - 14) / (16 * (2 + a * s) * (1 + s)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonneg_of_nonpos hs.le hbr
    · positivity
  linarith [log_div_antitone (le_refl 3) ha3]

/-- Degrees `a ≥ 8`: the rational part is at most `39/(80 a)` on `(0, 3/a]`. -/
theorem H_le_large {a s : ℝ} (ha8 : 8 ≤ a) (hs : 0 < s) (hsR : s ≤ 3 / a) :
    H a s ≤ Real.log 3 / 3 + 1 / 16 := by
  have ha : 0 < a := by linarith
  have h := H_le_aux ha hs
  have has : a * s ≤ 3 := mul_le_three ha hsR
  have has0 : 0 < a * s := mul_pos ha hs
  have hextra : s * ((9 * a - 32) * s - 14) / (16 * (2 + a * s) * (1 + s)) ≤ 39 / (80 * a) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 has) (by positivity : (0:ℝ) ≤ 720 * (a * s) + 416),
      mul_pos has0 hs, hs]
  have h39 : 39 / (80 * a) ≤ 39 / (80 * 8) := by gcongr
  have hl8 : Real.log a / a ≤ Real.log 8 / 8 := log_div_antitone (by norm_num) ha8
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h3 := log_three_ge
  have h2 := log_two_lt
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [h8] at hl8
  linarith

/-- `H b s ≤ (log b)/b + 27/(16 b) + 1/16` on `(0, 3/b]`. -/
theorem H_le_big {b s : ℝ} (hb : 0 < b) (hs : 0 < s) (hsR : s ≤ 3 / b) :
    H b s ≤ Real.log b / b + 27 / (16 * b) + 1 / 16 := by
  have hinv : 0 < 1 / b := by positivity
  have h1 : Real.log (1 / b) ≤ Real.log (1 / b + s) := Real.log_le_log hinv (by linarith)
  have h2 : Real.log (1 / b) = -Real.log b := by rw [one_div, Real.log_inv]
  have h3 : s / (1 + s) ≤ s := div_le_self hs.le (by linarith)
  have h4 : 9 / 16 * (3 / b) = 27 / (16 * b) := by field_simp; ring
  have hm := mul_le_mul_of_nonneg_left h1 hinv.le
  have e : Real.log b / b = 1 / b * Real.log b := by ring
  unfold H
  rw [e, ← h4]
  rw [h2] at hm
  nlinarith [hm, h3, hsR]

/-! ### The edge inequality when one end has degree at least 120 -/

theorem caseC_bound {a b : ℕ} {xu xv r : ℝ} (ha : 2 ≤ a) (hb : 120 ≤ b) (hr : 0 < r)
    (hρu : 0 < xu - 1 / (a:ℝ)) (hρv : 0 < xv - 1 / (b:ℝ))
    (I1 : r * (1 + r) = xu * xv)
    (hu2 : a = 2 → xu - 1 / (a:ℝ) ≤ 1) (hu3 : 3 ≤ a → xu - 1 / (a:ℝ) ≤ 3 / (a:ℝ))
    (hv3 : xv - 1 / (b:ℝ) ≤ 3 / (b:ℝ)) :
    Real.log (1 + r) - 1 / (a:ℝ) * Real.log xu - 1 / (b:ℝ) * Real.log xv
      - gp (xu - 1 / (a:ℝ)) * (r - (xu - 1 / (a:ℝ)))
      - gp (xv - 1 / (b:ℝ)) * (r - (xv - 1 / (b:ℝ)))
      ≤ 1 / 2 * Real.log (27 / 8) := by
  have haR : (2:ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (120:ℝ) ≤ b := by exact_mod_cast hb
  have ha0 : (0:ℝ) < a := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  have hinva : 0 < 1 / (a:ℝ) := by positivity
  have hinvb : 0 < 1 / (b:ℝ) := by positivity
  have hxv0 : 0 < xv := by linarith
  -- every end has `x ≤ 3/2`
  have hxu : xu ≤ 3 / 2 := by
    rcases Nat.eq_or_lt_of_le ha with h2 | h3
    · have h := hu2 h2.symm
      have e : (a:ℝ) = 2 := by exact_mod_cast h2.symm
      rw [e] at h
      linarith
    · have h := hu3 h3
      have ha3 : (3:ℝ) ≤ a := by exact_mod_cast h3
      have e : 3 / (a:ℝ) + 1 / (a:ℝ) = 4 / (a:ℝ) := by ring
      have e2 : 4 / (a:ℝ) ≤ 4 / 3 := by gcongr
      linarith
  -- an end of degree `b ≥ 3` has `x ≤ 4/b`
  have hxv : xv ≤ 4 / (b:ℝ) := by
    have e : 3 / (b:ℝ) + 1 / (b:ℝ) = 4 / (b:ℝ) := by ring
    linarith
  have hrle : r ≤ 6 / (b:ℝ) := by
    have h1 : r ≤ xu * xv := by nlinarith [mul_pos hr hr]
    have h2 : xu * xv ≤ 3 / 2 * (4 / (b:ℝ)) := mul_le_mul hxu hxv hxv0.le (by norm_num)
    have e : (3:ℝ) / 2 * (4 / (b:ℝ)) = 6 / (b:ℝ) := by ring
    linarith
  have hHu : H (a:ℝ) (xu - 1 / (a:ℝ)) ≤ Real.log 3 / 3 + 1 / 16 := by
    rcases Nat.eq_or_lt_of_le ha with h2 | h3
    · have e : (a:ℝ) = 2 := by exact_mod_cast h2.symm
      rw [e] at hρu ⊢
      exact H_two_le hρu
    · rcases Nat.lt_or_ge a 8 with h8 | h8
      · exact H_le_small (by exact_mod_cast h3) (by exact_mod_cast Nat.lt_succ_iff.1 h8) hρu
          (hu3 h3)
      · exact H_le_large (by exact_mod_cast h8) hρu (hu3 h3)
  have hHv := H_le_big hb0 hρv hv3
  have hE := edge_le_H (a := (a:ℝ)) (b := (b:ℝ)) (xu := xu) (xv := xv) hr hρu hρv
  -- numerics at `b ≥ 120`
  have h6 : 6 / (b:ℝ) ≤ 6 / 120 := by gcongr
  have h27 : 27 / (16 * (b:ℝ)) ≤ 27 / (16 * 120) := by gcongr
  have hlogb : Real.log b / b ≤ Real.log 120 / 120 := log_div_antitone (by norm_num) hbR
  have hlog120 : Real.log 120 ≤ 7 * Real.log 2 := by
    have h : Real.log 120 ≤ Real.log (2 ^ 7) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  have hL : Real.log (27 / 8) = 3 * Real.log 3 - 3 * Real.log 2 := by
    rw [show (27 / 8 : ℝ) = (3 / 2) ^ 3 by norm_num, Real.log_pow,
      Real.log_div (by norm_num) (by norm_num)]
    push_cast; ring
  have h3 := log_three_ge
  have h2 := log_two_lt
  rw [hL]
  linarith

end TreeEntropy
