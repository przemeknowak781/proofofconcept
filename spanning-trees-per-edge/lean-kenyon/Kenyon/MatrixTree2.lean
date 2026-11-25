import Kenyon.MatrixTree
import Kenyon.ForestCount

/-!
# From the number of spanning trees to the determinant (used for the sharpness)

* `det_redMat_eq_zero`  : with zero diagonal outside `R ≠ V` and no edge of `Es` with exactly
  one end in `R`, the determinant of `redMat Es R` vanishes;
* `det_le_numForests`   : `det (redMat Es R 0 z) ≤ z ^ (|V| − |R|) · numForests Es R`
  (with `numForests_le_det` this is the matrix-tree theorem for rooted forests);
* `det_redMat_expand`   : expansion of the determinant in the diagonal entries;
* `det_Kmat_le_numTrees`: in a connected multigraph, if `(1 − z) d_v ≤ y²` for every vertex,
  `0 ≤ z ≤ 1`, `0 ≤ y ≤ 1`, then `det K(z) ≤ numTrees · (1 + y) ^ (|V| + |E|)`.
-/

open Matrix Finset

namespace Kenyon

open TreeEntropy

variable {V E : Type} [Fintype V] [DecidableEq V]

theorem det_redMat_eq_zero (src tgt : E → V) {Es : Finset E} {R : Finset V} (z : ℝ) {x : V}
    (hx : x ∉ R)
    (hno : ¬ ∃ e ∈ Es, (src e ∉ R ∧ tgt e ∈ R) ∨ (tgt e ∉ R ∧ src e ∈ R)) :
    (redMat src tgt Es R (fun _ => 0) z).det = 0 := by
  rw [← exists_mulVec_eq_zero_iff]
  refine ⟨fun a => if a ∈ R then 0 else 1, ?_, ?_⟩
  · intro h
    have := congrFun h x
    simp [hx] at this
  · have hdot : ∀ e ∈ Es, ∑ b, incR src tgt R e b * (if b ∈ R then (0:ℝ) else 1) = 0 := by
      intro e he
      have hiff : src e ∈ R ↔ tgt e ∈ R := by
        constructor
        · intro h
          by_contra h'
          exact hno ⟨e, he, Or.inr ⟨h', h⟩⟩
        · intro h
          by_contra h'
          exact hno ⟨e, he, Or.inl ⟨h', h⟩⟩
      have hb : ∀ b, incR src tgt R e b * (if b ∈ R then (0:ℝ) else 1)
          = (if tgt e = b then (if b ∈ R then (0:ℝ) else 1) else 0)
            - (if src e = b then (if b ∈ R then (0:ℝ) else 1) else 0) := by
        intro b
        unfold incR inc
        by_cases hbR : b ∈ R <;> simp [hbR]
      rw [Finset.sum_congr rfl (fun b _ => hb b), Finset.sum_sub_distrib]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      by_cases h : src e ∈ R
      · simp [h, hiff.1 h]
      · have ht : tgt e ∉ R := fun h' => h (hiff.2 h')
        simp [h, ht]
    funext a
    simp only [mulVec, dotProduct, redMat, Matrix.add_apply, Matrix.smul_apply,
      Matrix.diagonal_apply, Matrix.sum_apply, vecMulVec_apply, smul_eq_mul, Pi.zero_apply]
    have h1 : ∀ b, ((if a = b then (if a ∈ R then (1:ℝ) else 0) else 0)
          + z * ∑ e ∈ Es, incR src tgt R e a * incR src tgt R e b)
          * (if b ∈ R then (0:ℝ) else 1)
        = (if a = b then (if a ∈ R then (1:ℝ) else 0) * (if b ∈ R then (0:ℝ) else 1) else 0)
          + z * ∑ e ∈ Es, incR src tgt R e a
            * (incR src tgt R e b * (if b ∈ R then (0:ℝ) else 1)) := by
      intro b
      rw [add_mul, mul_assoc, Finset.sum_mul]
      congr 1
      · split_ifs <;> simp
      · congr 1
        exact Finset.sum_congr rfl fun e _ => by ring
    rw [Finset.sum_congr rfl (fun b _ => h1 b), Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_comm]
    have h2 : ∑ e ∈ Es, ∑ b, incR src tgt R e a
        * (incR src tgt R e b * (if b ∈ R then (0:ℝ) else 1)) = 0 :=
      Finset.sum_eq_zero fun e he => by rw [← Finset.mul_sum, hdot e he, mul_zero]
    rw [h2, mul_zero, add_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    by_cases ha : a ∈ R <;> simp [ha]

/-- **The other half of the matrix-tree theorem for rooted forests.** -/
theorem det_le_numForests (src tgt : E → V) {z : ℝ} (hz : 0 ≤ z) :
    ∀ (n : ℕ) (Es : Finset E), Es.card = n → ∀ R : Finset V,
      (redMat src tgt Es R (fun _ => 0) z).det
        ≤ z ^ (Fintype.card V - R.card) * (numForests src tgt Es R : ℝ) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Es hEs R
    by_cases hR : R = univ
    · subst hR
      rw [redMat_univ, det_one, Finset.card_univ, Nat.sub_self, pow_zero, one_mul]
      exact_mod_cast one_le_numForests_univ src tgt Es
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
        rw [det_redMat_cross src tgt _ z he hu hc']
        have hf := numForests_ge src tgt he hu hc'
        have hfr : (numForests src tgt (Es.erase e) R : ℝ)
            + numForests src tgt (Es.erase e) (insert u R) ≤ numForests src tgt Es R := by
          exact_mod_cast hf
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
        rw [det_redMat_eq_zero src tgt z hx hcr]
        positivity

/-- **Expansion of the determinant in the diagonal entries.** -/
theorem det_redMat_expand (src tgt : E → V) (Es : Finset E) (c : V → ℝ) (z : ℝ)
    (S : Finset V) : ∀ R : Finset V,
      (redMat src tgt Es R (fun v => if v ∈ S then c v else 0) z).det
        = ∑ Q ∈ (S \ R).powerset,
            (∏ q ∈ Q, c q) * (redMat src tgt Es (R ∪ Q) (fun _ => 0) z).det := by
  induction S using Finset.induction_on with
  | empty =>
    intro R
    simp
  | insert a S ha ih =>
    intro R
    by_cases haR : a ∈ R
    · have h1 : redMat src tgt Es R (fun v => if v ∈ insert a S then c v else 0) z
          = redMat src tgt Es R (fun v => if v ∈ S then c v else 0) z := by
        unfold redMat
        congr 2
        funext v
        by_cases hv : v ∈ R
        · simp [hv]
        · have hva : v ≠ a := fun h => hv (h ▸ haR)
          simp [hv, Finset.mem_insert, hva]
      rw [h1, ih R, Finset.insert_sdiff_of_mem _ haR]
    · have h1 : redMat src tgt Es R (fun v => if v ∈ insert a S then c v else 0) z
          = redMat src tgt Es R (fun v => if v ∈ S then c v else 0) z
            + c a • diagonal (Pi.single a (1:ℝ)) := by
        ext x y
        simp only [redMat, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply,
          Pi.single_apply, smul_eq_mul, Finset.mem_insert]
        by_cases hxy : x = y
        · subst hxy
          by_cases hxa : x = a
          · subst hxa
            simp [haR, ha]
            ring
          · simp [hxa]
        · simp [hxy]
      have hsd : S \ insert a R = S \ R := by
        ext v
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun h => h2 (Or.inr h)⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun h => h.elim (fun h' => ha (h' ▸ h1)) h2⟩
      have haSR : a ∉ S \ R := fun h => ha (Finset.mem_sdiff.1 h).1
      rw [h1, det_add_smul_single, pin_redMat, ih R, ih (insert a R),
        Finset.insert_sdiff_of_notMem _ haR, Finset.sum_powerset_insert haSR, hsd,
        Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun Q hQ => ?_
      have haQ : a ∉ Q := fun h => ha (Finset.mem_sdiff.1 (Finset.mem_powerset.1 hQ h)).1
      rw [Finset.prod_insert haQ, Finset.insert_union, Finset.union_insert]
      ring

omit [DecidableEq V] in
theorem sum_pow_card (α : Type) [Fintype α] (y : ℝ) :
    ∑ Q : Finset α, y ^ Q.card = (1 + y) ^ Fintype.card α := by
  have h := Finset.sum_pow_mul_eq_add_pow y 1 (univ : Finset α)
  simp only [one_pow, mul_one, Finset.powerset_univ, Finset.card_univ] at h
  rw [h, add_comm]

/-- **From the number of spanning trees to the determinant.** -/
theorem det_Kmat_le_numTrees [Fintype E] [Nonempty V] (src tgt : E → V)
    (hconn : ∀ x y, Conn src tgt univ x y) {z y : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hc : ∀ v, (1 - z) * (deg src tgt v : ℝ) ≤ y ^ 2) :
    (Kmat src tgt z).det
      ≤ (numTrees src tgt : ℝ) * (1 + y) ^ (Fintype.card V + Fintype.card E) := by
  classical
  set c : V → ℝ := fun v => (1 - z) * (deg src tgt v : ℝ) with hcdef
  have hc0 : ∀ v, 0 ≤ c v := fun v => mul_nonneg (sub_nonneg.2 hz1) (Nat.cast_nonneg _)
  have hτ : (0:ℝ) ≤ numTrees src tgt := Nat.cast_nonneg _
  have h1 : Kmat src tgt z
      = redMat src tgt univ ∅ (fun v => if v ∈ (univ : Finset V) then c v else 0) z := by
    rw [Kmat_eq_redMat]
    simp [hcdef]
  rw [h1, det_redMat_expand src tgt univ c z univ ∅]
  simp only [Finset.sdiff_empty, Finset.empty_union, Finset.powerset_univ]
  have hterm : ∀ Q : Finset V,
      (∏ q ∈ Q, c q) * (redMat src tgt univ Q (fun _ => 0) z).det
        ≤ (numTrees src tgt : ℝ) * ∑ S : Finset E, y ^ Q.card * y ^ S.card := by
    intro Q
    have hprod0 : 0 ≤ ∏ q ∈ Q, c q := Finset.prod_nonneg fun q _ => hc0 q
    have hprod : ∏ q ∈ Q, c q ≤ (y ^ 2) ^ Q.card := by
      calc ∏ q ∈ Q, c q ≤ ∏ _q ∈ Q, y ^ 2 :=
            Finset.prod_le_prod₀ (fun q _ => hc0 q) (fun q _ => hc q)
        _ = (y ^ 2) ^ Q.card := by simp
    have hdet0 := (redMat_posSemidef src tgt (univ : Finset E) Q (c := fun _ => (0:ℝ))
      (fun _ => le_rfl) hz0).det_nonneg
    have hdet := det_le_numForests src tgt hz0 _ (univ : Finset E) rfl Q
    have hzp : z ^ (Fintype.card V - Q.card) ≤ 1 := pow_le_one₀ hz0 hz1
    have hf0 : (0:ℝ) ≤ numForests src tgt univ Q := Nat.cast_nonneg _
    have hdet' : (redMat src tgt univ Q (fun _ => 0) z).det ≤ numForests src tgt univ Q := by
      nlinarith [mul_le_mul_of_nonneg_right hzp hf0]
    have hrhs0 : 0 ≤ ∑ S : Finset E, y ^ Q.card * y ^ S.card :=
      Finset.sum_nonneg fun S _ => by positivity
    by_cases hQ : Q.Nonempty
    · have hF : (numForests src tgt univ Q : ℝ) ≤ (numTrees src tgt : ℝ)
          * ((univ : Finset (Finset E)).filter fun S => S.card + 1 = Q.card).card := by
        exact_mod_cast numForests_le_numTrees_mul src tgt hconn hQ
      have hsum : (y ^ 2) ^ Q.card
          * (((univ : Finset (Finset E)).filter fun S => S.card + 1 = Q.card).card : ℝ)
          ≤ ∑ S : Finset E, y ^ Q.card * y ^ S.card := by
        have hA : (((univ : Finset (Finset E)).filter fun S => S.card + 1 = Q.card).card : ℝ)
            = ∑ _S ∈ (univ : Finset (Finset E)).filter (fun S => S.card + 1 = Q.card), (1:ℝ) := by
          simp
        rw [hA, Finset.mul_sum]
        calc ∑ S ∈ (univ : Finset (Finset E)).filter (fun S => S.card + 1 = Q.card),
              (y ^ 2) ^ Q.card * (1:ℝ)
            ≤ ∑ S ∈ (univ : Finset (Finset E)).filter (fun S => S.card + 1 = Q.card),
              y ^ Q.card * y ^ S.card := by
              refine Finset.sum_le_sum fun S hS => ?_
              have hS' : S.card + 1 = Q.card := (Finset.mem_filter.1 hS).2
              rw [mul_one, ← pow_mul, ← pow_add]
              exact pow_le_pow_of_le_one hy0 hy1 (by omega)
          _ ≤ ∑ S : Finset E, y ^ Q.card * y ^ S.card :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun S _ _ => by positivity)
      calc (∏ q ∈ Q, c q) * (redMat src tgt univ Q (fun _ => 0) z).det
          ≤ (y ^ 2) ^ Q.card * (numForests src tgt univ Q : ℝ) :=
            mul_le_mul hprod hdet' hdet0 (by positivity)
        _ ≤ (y ^ 2) ^ Q.card * ((numTrees src tgt : ℝ)
            * ((univ : Finset (Finset E)).filter fun S => S.card + 1 = Q.card).card) :=
            mul_le_mul_of_nonneg_left hF (by positivity)
        _ = (numTrees src tgt : ℝ) * ((y ^ 2) ^ Q.card
            * ((univ : Finset (Finset E)).filter fun S => S.card + 1 = Q.card).card) := by ring
        _ ≤ (numTrees src tgt : ℝ) * ∑ S : Finset E, y ^ Q.card * y ^ S.card :=
            mul_le_mul_of_nonneg_left hsum hτ
    · rw [Finset.not_nonempty_iff_eq_empty] at hQ
      subst hQ
      have h0 : numForests src tgt (univ : Finset E) (∅ : Finset V) = 0 := by
        obtain ⟨x⟩ := ‹Nonempty V›
        unfold numForests
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro F _ hF
        obtain ⟨ρ, hρ, -⟩ := hF.2 x
        exact absurd hρ (Finset.notMem_empty ρ)
      rw [h0] at hdet'
      have hz' : (redMat src tgt (univ : Finset E) (∅ : Finset V) (fun _ => 0) z).det = 0 :=
        le_antisymm (by simpa using hdet') hdet0
      rw [hz', mul_zero]
      exact mul_nonneg hτ hrhs0
  calc ∑ Q : Finset V, (∏ q ∈ Q, c q) * (redMat src tgt univ Q (fun _ => 0) z).det
      ≤ ∑ Q : Finset V, (numTrees src tgt : ℝ) * ∑ S : Finset E, y ^ Q.card * y ^ S.card :=
        Finset.sum_le_sum fun Q _ => hterm Q
    _ = (numTrees src tgt : ℝ)
        * ((∑ Q : Finset V, y ^ Q.card) * (∑ S : Finset E, y ^ S.card)) := by
        rw [← Finset.mul_sum, Finset.sum_mul_sum]
    _ = (numTrees src tgt : ℝ) * (1 + y) ^ (Fintype.card V + Fintype.card E) := by
        rw [sum_pow_card, sum_pow_card, ← pow_add]

end Kenyon
