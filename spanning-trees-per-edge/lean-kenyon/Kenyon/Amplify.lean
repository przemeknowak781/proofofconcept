import Kenyon.Count

/-!
# Removing the polynomial factor: copies glued at a vertex

`GlueV r N` is the vertex set of `N + 1` copies of the multigraph glued at the vertex `r`
(`none` is the common vertex, `some (v, i)` is the vertex `v ≠ r` of the copy `i`); the edges
are `E × Fin (N + 1)`.

* `two_le_deg_glue`, `no22_glue` : the two conditions on the degrees pass to the glued graph;
* `numTrees_pow_le`  : `numTrees ^ (N + 1) ≤ numTrees (glued graph)`;
* `numTrees_le_exp_classC` : `numTrees ≤ exp (|E| · (1/2) · log (27/8))` when every degree is at
  least `2` and no edge joins two vertices of degree `2`.
-/

open Finset

namespace Kenyon

open TreeEntropy

variable {V E : Type} [Fintype E] [Fintype V] [DecidableEq V]

/-- The vertices of `N + 1` copies glued at `r`. -/
abbrev GlueV (r : V) (N : ℕ) : Type := Option ({v : V // v ≠ r} × Fin (N + 1))

/-- The vertex `v` of the copy `i`. -/
def glue (r : V) (N : ℕ) (v : V) (i : Fin (N + 1)) : GlueV r N :=
  if h : v = r then none else some (⟨v, h⟩, i)

/-- An end map of the glued graph. -/
def gmap (f : E → V) (r : V) (N : ℕ) (p : E × Fin (N + 1)) : GlueV r N :=
  glue r N (f p.1) p.2

omit [Fintype V] in
theorem glue_root (r : V) (N : ℕ) (i : Fin (N + 1)) : glue r N r i = none := by
  simp [glue]

omit [Fintype V] in
theorem exists_glue (r : V) (N : ℕ) (w : GlueV r N) : ∃ v i, w = glue r N v i := by
  rcases w with _ | ⟨⟨v, h⟩, i⟩
  · exact ⟨r, 0, (glue_root r N 0).symm⟩
  · exact ⟨v, i, by simp [glue, h]⟩

omit [Fintype V] in
theorem deg_le_deg_glue (src tgt : E → V) (r : V) (N : ℕ) (v : V) (i : Fin (N + 1)) :
    deg src tgt v ≤ deg (gmap src r N) (gmap tgt r N) (glue r N v i) := by
  unfold deg
  refine Nat.add_le_add ?_ ?_
  · refine Finset.card_le_card_of_injOn (fun e => (e, i)) ?_ ?_
    · intro e he
      rw [Finset.mem_coe, Finset.mem_filter] at he
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simp [gmap, he.2]⟩
    · intro e _ e' _ h
      exact (Prod.mk.inj h).1
  · refine Finset.card_le_card_of_injOn (fun e => (e, i)) ?_ ?_
    · intro e he
      rw [Finset.mem_coe, Finset.mem_filter] at he
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simp [gmap, he.2]⟩
    · intro e _ e' _ h
      exact (Prod.mk.inj h).1

section ClassC

variable {src tgt : E → V} (hdeg : ∀ v, 2 ≤ deg src tgt v)
  (hD : ∀ e, ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2))

omit [Fintype V] in
include hdeg in
theorem two_le_deg_glue (r : V) (N : ℕ) (w : GlueV r N) :
    2 ≤ deg (gmap src r N) (gmap tgt r N) w := by
  obtain ⟨v, i, rfl⟩ := exists_glue r N w
  exact (hdeg v).trans (deg_le_deg_glue src tgt r N v i)

omit [Fintype V] in
include hdeg hD in
theorem no22_glue (r : V) (N : ℕ) (p : E × Fin (N + 1)) :
    ¬(deg (gmap src r N) (gmap tgt r N) (gmap src r N p) = 2
      ∧ deg (gmap src r N) (gmap tgt r N) (gmap tgt r N p) = 2) := by
  rintro ⟨h1, h2⟩
  have a1 := deg_le_deg_glue src tgt r N (src p.1) p.2
  have a2 := deg_le_deg_glue src tgt r N (tgt p.1) p.2
  have b1 := hdeg (src p.1)
  have b2 := hdeg (tgt p.1)
  refine hD p.1 ⟨?_, ?_⟩
  · have : deg (gmap src r N) (gmap tgt r N) (glue r N (src p.1) p.2) = 2 := h1
    omega
  · have : deg (gmap src r N) (gmap tgt r N) (glue r N (tgt p.1) p.2) = 2 := h2
    omega

end ClassC

theorem card_glueV (r : V) (N : ℕ) :
    Fintype.card (GlueV r N) = (Fintype.card V - 1) * (N + 1) + 1 := by
  have h : Fintype.card {v : V // v ≠ r} = Fintype.card V - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rw [Fintype.card_option, Fintype.card_prod, h, Fintype.card_fin]

open scoped Classical in
/-- The edge set of the glued graph made of one edge set in each copy. -/
noncomputable def glueSet (N : ℕ) (T : Fin (N + 1) → Finset E) : Finset (E × Fin (N + 1)) :=
  univ.filter fun p => p.1 ∈ T p.2

omit [Fintype V] [DecidableEq V] in
theorem mem_glueSet (N : ℕ) (T : Fin (N + 1) → Finset E) (p : E × Fin (N + 1)) :
    p ∈ glueSet N T ↔ p.1 ∈ T p.2 := by
  simp [glueSet]

omit [Fintype V] [DecidableEq V] in
theorem card_glueSet (N : ℕ) (T : Fin (N + 1) → Finset E) :
    (glueSet N T).card = ∑ i, (T i).card := by
  classical
  unfold glueSet
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem isTree_glueSet (src tgt : E → V) (r : V) (N : ℕ) (T : Fin (N + 1) → Finset E)
    (hT : ∀ i, IsTree src tgt (T i)) :
    IsTree (gmap src r N) (gmap tgt r N) (glueSet N T) := by
  have hroot : ∀ w : GlueV r N,
      Conn (gmap src r N) (gmap tgt r N) (glueSet N T) w none := by
    intro w
    obtain ⟨v, i, rfl⟩ := exists_glue r N w
    have hconn := (hT i).2 v r
    have hlift : ∀ b, Conn src tgt (T i) v b →
        Conn (gmap src r N) (gmap tgt r N) (glueSet N T) (glue r N v i) (glue r N b i) := by
      intro b hb
      induction hb with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih =>
        obtain ⟨e, he, h⟩ := hbc
        refine Relation.ReflTransGen.tail ih ⟨(e, i), (mem_glueSet N T (e, i)).2 he, ?_⟩
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by simp [gmap, h1], by simp [gmap, h2]⟩
        · exact Or.inr ⟨by simp [gmap, h1], by simp [gmap, h2]⟩
    have h := hlift r hconn
    rw [glue_root] at h
    exact h
  refine ⟨?_, fun w w' => (hroot w).trans (hroot w').symm⟩
  rw [card_glueSet, card_glueV]
  have hc : ∀ i, (T i).card = Fintype.card V - 1 := by
    intro i
    have := (hT i).1
    omega
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- **The number of spanning trees is supermultiplicative under gluing.** -/
theorem numTrees_pow_le (src tgt : E → V) (r : V) (N : ℕ) :
    numTrees src tgt ^ (N + 1) ≤ numTrees (gmap src r N) (gmap tgt r N) := by
  classical
  have hc1 : Fintype.card {T : Finset E // IsTree src tgt T} = numTrees src tgt :=
    Fintype.card_of_subtype _ (fun T => by simp)
  have hc2 : Fintype.card {S : Finset (E × Fin (N + 1)) //
      IsTree (gmap src r N) (gmap tgt r N) S} = numTrees (gmap src r N) (gmap tgt r N) :=
    Fintype.card_of_subtype _ (fun T => by simp)
  let Φ : (Fin (N + 1) → {T : Finset E // IsTree src tgt T}) →
      {S : Finset (E × Fin (N + 1)) // IsTree (gmap src r N) (gmap tgt r N) S} :=
    fun T => ⟨glueSet N (fun i => (T i).1), isTree_glueSet src tgt r N _ (fun i => (T i).2)⟩
  have hinj : Function.Injective Φ := by
    intro T T' h
    funext i
    apply Subtype.ext
    ext e
    have h' : glueSet N (fun i => (T i).1) = glueSet N (fun i => (T' i).1) :=
      congrArg Subtype.val h
    have h1 : (e, i) ∈ glueSet N (fun i => (T i).1) ↔ (e, i) ∈ glueSet N (fun i => (T' i).1) := by
      rw [h']
    simpa [mem_glueSet] using h1
  have hle := Fintype.card_le_of_injective Φ hinj
  rw [Fintype.card_fun, Fintype.card_fin, hc1, hc2] at hle
  exact hle

section ClassC

variable {src tgt : E → V} (hdeg : ∀ v, 2 ≤ deg src tgt v)
  (hD : ∀ e, ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2))

include hdeg hD in
/-- **The bound for the class**, without the polynomial factor. -/
theorem numTrees_le_exp_classC (r : V) :
    (numTrees src tgt : ℝ) ≤ Real.exp ((Fintype.card E : ℝ) * (1 / 2 * Real.log (27 / 8))) := by
  set X : ℝ := Real.exp ((Fintype.card E : ℝ) * (1 / 2 * Real.log (27 / 8))) with hX
  have hX0 : 0 < X := Real.exp_pos _
  have key : ∀ M : ℕ, 0 < M → ((numTrees src tgt : ℝ) / X) ^ M
      ≤ ((Fintype.card V : ℝ) ^ 2 * Real.exp 3) * (M:ℝ) ^ 2 := by
    intro M hM
    obtain ⟨N, rfl⟩ : ∃ N, M = N + 1 := ⟨M - 1, by omega⟩
    have h1 : ((numTrees src tgt : ℝ)) ^ (N + 1)
        ≤ (numTrees (gmap src r N) (gmap tgt r N) : ℝ) := by
      exact_mod_cast numTrees_pow_le src tgt r N
    have h2 := numTrees_le_classC (two_le_deg_glue hdeg r N) (no22_glue hdeg hD r N)
      (none : GlueV r N)
    have hcardV : (Fintype.card (GlueV r N) : ℝ) ≤ (Fintype.card V : ℝ) * ((N + 1 : ℕ) : ℝ) := by
      have hcard : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨r⟩
      have : Fintype.card (GlueV r N) ≤ Fintype.card V * (N + 1) := by
        rw [card_glueV]
        have : (Fintype.card V - 1) * (N + 1) + (N + 1) = Fintype.card V * (N + 1) := by
          have : Fintype.card V = (Fintype.card V - 1) + 1 := by omega
          nth_rewrite 2 [this]
          ring
        omega
      exact_mod_cast this
    have hE : (Fintype.card (E × Fin (N + 1)) : ℝ) * (1 / 2 * Real.log (27 / 8))
        = ((N + 1 : ℕ) : ℝ) * ((Fintype.card E : ℝ) * (1 / 2 * Real.log (27 / 8))) := by
      rw [Fintype.card_prod, Fintype.card_fin]
      push_cast
      ring
    rw [hE, Real.exp_natCast_mul] at h2
    rw [div_pow, div_le_iff₀ (pow_pos hX0 _)]
    have hsq : (Fintype.card (GlueV r N) : ℝ) ^ 2
        ≤ ((Fintype.card V : ℝ) * ((N + 1 : ℕ) : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hcardV 2
    have hpos : 0 ≤ Real.exp 3 * X ^ (N + 1) := by positivity
    calc (numTrees src tgt : ℝ) ^ (N + 1)
        ≤ (numTrees (gmap src r N) (gmap tgt r N) : ℝ) := h1
      _ ≤ (Fintype.card (GlueV r N) : ℝ) ^ 2 * (Real.exp 3 * X ^ (N + 1)) := h2
      _ ≤ ((Fintype.card V : ℝ) * ((N + 1 : ℕ) : ℝ)) ^ 2 * (Real.exp 3 * X ^ (N + 1)) :=
          mul_le_mul_of_nonneg_right hsq hpos
      _ = (Fintype.card V : ℝ) ^ 2 * Real.exp 3 * ((N + 1 : ℕ) : ℝ) ^ 2 * X ^ (N + 1) := by ring
  have h := le_one_of_pow_le key
  rwa [div_le_one hX0] at h

end ClassC

end Kenyon
