import Kenyon.Lap
import Kenyon.Forest

/-!
# From the determinant to the number of spanning trees

`redMat Es R c z` is the matrix

    diagonal (1 on R, c outside R) + z · ∑ e ∈ Es, w_e ⊗ w_e,

where `w_e` is the incidence vector of `e` with the entries in `R` set to zero. It is the matrix
`diagonal c + z · L_Es` with the rows and columns of `R` replaced by those of the identity.

* `det_redMat_cross` : for an edge `e ∈ Es` with one end `u ∉ R` and the other end in `R`,
  `det (redMat Es R) = det (redMat (Es − e) R) + z · det (redMat (Es − e) (R ∪ {u}))`;
* `numForests_le_det` : `z ^ (|V| − |R|) · numForests Es R ≤ det (redMat Es R c z)` for `c, z ≥ 0`
  (the inequality half of the matrix-tree theorem for rooted forests);
* `det_Kmat_ge` : `(1 − z) · d_r · z ^ (|V| − 1) · numTrees ≤ det K(z)` for `0 ≤ z ≤ 1`.
-/

open Matrix Finset

namespace Kenyon

open TreeEntropy

variable {V E : Type} [Fintype V] [DecidableEq V]

/-- Replace the row `u` and the column `u` by those of the identity matrix. -/
def pin (M : Matrix V V ℝ) (u : V) : Matrix V V ℝ :=
  Matrix.of fun a b => if a = u ∨ b = u then (if a = b then 1 else 0) else M a b

theorem det_updateRow_single_eq_pin (M : Matrix V V ℝ) (u : V) :
    (updateRow M u (Pi.single u (1:ℝ))).det = (pin M u).det := by
  set M' := updateRow M u (Pi.single u (1:ℝ)) with hM'
  set r : V → ℝ := fun a => if a = u then 0 else M a u with hr
  have hpin : pin M u = updateCol M' u (Pi.single u 1) := by
    ext a b
    simp only [pin, of_apply, updateCol_apply, hM', updateRow_apply, Pi.single_apply]
    by_cases ha : a = u
    · subst ha
      by_cases hb : b = a
      · subst hb
        simp
      · have hb' : a ≠ b := fun h => hb h.symm
        simp [hb, hb']
    · by_cases hb : b = u
      · subst hb
        simp [ha]
      · simp [ha, hb]
  have hcol : M' = updateCol M' u (Pi.single u 1 + r) := by
    ext a b
    simp only [updateCol_apply, hM', updateRow_apply, Pi.add_apply, Pi.single_apply, hr]
    by_cases ha : a = u <;> by_cases hb : b = u <;> simp [ha, hb]
  have hzero : (updateCol M' u r).det = 0 := by
    apply det_eq_zero_of_row_eq_zero u
    intro b
    simp only [updateCol_apply, hM', updateRow_apply, hr, Pi.single_apply]
    by_cases hb : b = u <;> simp [hb]
  rw [hpin]
  conv_lhs => rw [hcol]
  rw [det_updateCol_add, hzero, add_zero]

/-- The determinant is affine in a diagonal entry. -/
theorem det_add_smul_single (M : Matrix V V ℝ) (u : V) (z : ℝ) :
    (M + z • diagonal (Pi.single u (1:ℝ))).det = M.det + z * (pin M u).det := by
  have h1 : M + z • diagonal (Pi.single u (1:ℝ))
      = updateRow M u (M u + z • Pi.single u 1) := by
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, updateRow_apply,
      Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases ha : a = u
    · subst ha
      by_cases hab : a = b
      · subst hab
        simp
      · have hba : b ≠ a := fun h => hab h.symm
        simp [hab, hba]
    · simp [ha]
  rw [h1, det_updateRow_add, updateRow_eq_self, det_updateRow_smul, det_updateRow_single_eq_pin]

/-- The incidence vector with the entries in `R` set to zero. -/
def incR (src tgt : E → V) (R : Finset V) (e : E) (a : V) : ℝ :=
  if a ∈ R then 0 else inc src tgt e a

/-- `diagonal c + z · L_Es` with the rows and columns of `R` replaced by those of the identity. -/
def redMat (src tgt : E → V) (Es : Finset E) (R : Finset V) (c : V → ℝ) (z : ℝ) :
    Matrix V V ℝ :=
  diagonal (fun a => if a ∈ R then 1 else c a)
    + z • ∑ e ∈ Es, vecMulVec (incR src tgt R e) (incR src tgt R e)

omit [Fintype V] in
theorem redMat_posSemidef (src tgt : E → V) (Es : Finset E) (R : Finset V) {c : V → ℝ}
    (hc : ∀ a, 0 ≤ c a) {z : ℝ} (hz : 0 ≤ z) : (redMat src tgt Es R c z).PosSemidef := by
  unfold redMat
  refine PosSemidef.add (PosSemidef.diagonal fun a => ?_) (PosSemidef.smul ?_ hz)
  · show (0:ℝ) ≤ if a ∈ R then 1 else c a
    split_ifs
    · exact zero_le_one
    · exact hc a
  · exact posSemidef_sum _ fun e _ => by
      simpa using posSemidef_vecMulVec_self_star (incR src tgt R e)

theorem redMat_univ (src tgt : E → V) (Es : Finset E) (c : V → ℝ) (z : ℝ) :
    redMat src tgt Es univ c z = 1 := by
  have h0 : ∀ e, incR src tgt (univ : Finset V) e = 0 := by
    intro e
    funext a
    simp [incR]
  unfold redMat
  simp [h0]

omit [Fintype V] in
theorem pin_redMat (src tgt : E → V) (Es : Finset E) (R : Finset V) (c : V → ℝ) (z : ℝ)
    (u : V) : pin (redMat src tgt Es R c z) u = redMat src tgt Es (insert u R) c z := by
  ext a b
  simp only [pin, of_apply, redMat, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply,
    Matrix.sum_apply, vecMulVec_apply, incR, smul_eq_mul, Finset.mem_insert]
  by_cases ha : a = u
  · subst ha
    simp
  · by_cases hb : b = u
    · subst hb
      simp [ha]
    · simp [ha, hb]

omit [Fintype V] in
theorem redMat_eq_erase_add [DecidableEq E] (src tgt : E → V) {Es : Finset E} {R : Finset V}
    (c : V → ℝ) (z : ℝ) {e : E} (he : e ∈ Es) {u : V} (hu : u ∉ R)
    (hc : (src e = u ∧ tgt e ∈ R) ∨ (tgt e = u ∧ src e ∈ R)) :
    redMat src tgt Es R c z
      = redMat src tgt (Es.erase e) R c z + z • diagonal (Pi.single u (1:ℝ)) := by
  have hv : vecMulVec (incR src tgt R e) (incR src tgt R e) = diagonal (Pi.single u (1:ℝ)) := by
    have hinc : ∃ s : ℝ, s * s = 1 ∧ incR src tgt R e = fun a => if a = u then s else 0 := by
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨-1, by norm_num, ?_⟩
        funext a
        unfold incR inc
        by_cases ha : a ∈ R
        · have : a ≠ u := fun h => hu (h ▸ ha)
          simp [ha, this]
        · have h3 : tgt e ≠ a := fun h => ha (h ▸ h2)
          by_cases hau : a = u
          · subst hau
            simp [ha, h3, h1]
          · have : src e ≠ a := fun h => hau (h.symm.trans h1)
            simp [ha, h3, hau, this]
      · refine ⟨1, by norm_num, ?_⟩
        funext a
        unfold incR inc
        by_cases ha : a ∈ R
        · have : a ≠ u := fun h => hu (h ▸ ha)
          simp [ha, this]
        · have h3 : src e ≠ a := fun h => ha (h ▸ h2)
          by_cases hau : a = u
          · subst hau
            simp [ha, h3, h1]
          · have : tgt e ≠ a := fun h => hau (h.symm.trans h1)
            simp [ha, h3, hau, this]
    obtain ⟨s, hs, hinc⟩ := hinc
    rw [hinc]
    ext a b
    simp only [vecMulVec_apply, Matrix.diagonal_apply, Pi.single_apply]
    by_cases ha : a = u
    · subst ha
      by_cases hb : b = a
      · subst hb
        simp [hs]
      · have hb' : a ≠ b := fun h => hb h.symm
        simp [hb, hb']
    · simp [ha]
  unfold redMat
  rw [← Finset.add_sum_erase Es _ he, hv, smul_add]
  abel

theorem det_redMat_cross [DecidableEq E] (src tgt : E → V) {Es : Finset E} {R : Finset V}
    (c : V → ℝ) (z : ℝ) {e : E} (he : e ∈ Es) {u : V} (hu : u ∉ R)
    (hc : (src e = u ∧ tgt e ∈ R) ∨ (tgt e = u ∧ src e ∈ R)) :
    (redMat src tgt Es R c z).det
      = (redMat src tgt (Es.erase e) R c z).det
        + z * (redMat src tgt (Es.erase e) (insert u R) c z).det := by
  rw [redMat_eq_erase_add src tgt c z he hu hc, det_add_smul_single, pin_redMat]

/-- **The inequality half of the matrix-tree theorem for rooted forests.** -/
theorem numForests_le_det (src tgt : E → V) {c : V → ℝ} (hc : ∀ a, 0 ≤ c a) {z : ℝ}
    (hz : 0 ≤ z) : ∀ (n : ℕ) (Es : Finset E), Es.card = n → ∀ R : Finset V,
      z ^ (Fintype.card V - R.card) * (numForests src tgt Es R : ℝ)
        ≤ (redMat src tgt Es R c z).det := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Es hEs R
    by_cases hR : R = univ
    · subst hR
      rw [redMat_univ, det_one, Finset.card_univ, Nat.sub_self, pow_zero, one_mul]
      exact_mod_cast numForests_univ_le src tgt Es
    · by_cases hcr : ∃ e ∈ Es, (src e ∉ R ∧ tgt e ∈ R) ∨ (tgt e ∉ R ∧ src e ∈ R)
      · obtain ⟨e, he, hcr⟩ := hcr
        obtain ⟨u, hu, hc'⟩ :
            ∃ u, u ∉ R ∧ ((src e = u ∧ tgt e ∈ R) ∨ (tgt e = u ∧ src e ∈ R)) := by
          rcases hcr with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨src e, h1, Or.inl ⟨rfl, h2⟩⟩
          · exact ⟨tgt e, h1, Or.inr ⟨rfl, h2⟩⟩
        have hcard : (Es.erase e).card < n := by
          rw [Finset.card_erase_of_mem he]
          have := Finset.card_pos.2 ⟨e, he⟩
          omega
        have i1 := ih _ hcard (Es.erase e) rfl R
        have i2 := ih _ hcard (Es.erase e) rfl (insert u R)
        rw [det_redMat_cross src tgt c z he hu hc']
        have hf := numForests_le src tgt (Es := Es) (e := e) hu hc'
        have hfr : (numForests src tgt Es R : ℝ) ≤ numForests src tgt (Es.erase e) R
            + numForests src tgt (Es.erase e) (insert u R) := by exact_mod_cast hf
        have hk : Fintype.card V - R.card = (Fintype.card V - (insert u R).card) + 1 := by
          rw [Finset.card_insert_of_notMem hu]
          have : R.card < Fintype.card V := Finset.card_lt_univ_of_notMem hu
          omega
        rw [hk, pow_succ] at i1 ⊢
        have hzk : 0 ≤ z ^ (Fintype.card V - (insert u R).card) * z := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hfr hzk, mul_le_mul_of_nonneg_left i2 hz]
      · obtain ⟨x, hx⟩ : ∃ x, x ∉ R := by
          by_contra h
          exact hR (Finset.eq_univ_iff_forall.2 fun x => by_contra fun hx => h ⟨x, hx⟩)
        rw [numForests_eq_zero src tgt hx hcr]
        simp only [Nat.cast_zero, mul_zero]
        exact (redMat_posSemidef src tgt Es R hc hz).det_nonneg

omit [Fintype V] in
theorem incR_empty (src tgt : E → V) (e : E) : incR src tgt ∅ e = inc src tgt e := by
  funext a
  simp [incR]

omit [Fintype V] in
theorem Kmat_eq_redMat [Fintype E] (src tgt : E → V) (z : ℝ) :
    Kmat src tgt z = redMat src tgt univ ∅ (fun v => (1 - z) * (deg src tgt v : ℝ)) z := by
  unfold Kmat redMat lap
  simp [incR_empty]

/-- **From the determinant to the number of spanning trees.** -/
theorem det_Kmat_ge [Fintype E] (src tgt : E → V) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (r : V) :
    (1 - z) * (deg src tgt r : ℝ) * (z ^ (Fintype.card V - 1) * (numTrees src tgt : ℝ))
      ≤ (Kmat src tgt z).det := by
  set c : V → ℝ := fun v => (1 - z) * (deg src tgt v : ℝ) with hc
  have hc0 : ∀ a, 0 ≤ c a := fun a => mul_nonneg (sub_nonneg.2 hz1) (Nat.cast_nonneg _)
  set c' : V → ℝ := Function.update c r 0 with hc'
  have hc'0 : ∀ a, 0 ≤ c' a := by
    intro a
    simp only [hc', Function.update_apply]
    split_ifs
    · exact le_rfl
    · exact hc0 a
  have hsplit : redMat src tgt univ ∅ c z
      = redMat src tgt univ ∅ c' z + c r • diagonal (Pi.single r (1:ℝ)) := by
    ext a b
    simp only [redMat, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply,
      Finset.notMem_empty, ite_false, hc', Function.update_apply, Pi.single_apply, smul_eq_mul]
    by_cases hab : a = b
    · subst hab
      by_cases ha : a = r
      · subst ha
        simp
        ring
      · simp [ha]
    · simp [hab]
  rw [Kmat_eq_redMat, hsplit, det_add_smul_single, pin_redMat]
  have h0 := (redMat_posSemidef src tgt univ ∅ hc'0 hz0).det_nonneg
  have h1 := numForests_le_det src tgt hc'0 hz0 _ univ rfl (insert r ∅)
  have h2 : (numTrees src tgt : ℝ) ≤ numForests src tgt univ (insert r ∅) := by
    exact_mod_cast numTrees_le_numForests src tgt r
  have hcard : Fintype.card V - (insert r (∅ : Finset V)).card = Fintype.card V - 1 := by simp
  rw [hcard] at h1
  have hzn : 0 ≤ z ^ (Fintype.card V - 1) := by positivity
  have h3 := mul_le_mul_of_nonneg_left h2 hzn
  have h4 := mul_le_mul_of_nonneg_left (h3.trans h1) (hc0 r)
  simp only [hc] at h4 ⊢
  linarith

end Kenyon
