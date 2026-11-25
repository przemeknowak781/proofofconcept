import Kenyon.Forest
import TreeEntropy.Sum

/-!
# Deleting and contracting an edge

For an edge `e` of a multigraph `src tgt : E → V`:

* `dmap src e`, `dmap tgt e` are the end maps of `G − e` (edges `{e' // e' ≠ e}`);
* for a non-loop `f` with ends `x ≠ y`, `cmap src f x y`, `cmap tgt f x y` are the end maps of
  `G / f` (vertices `{v // v ≠ y}`, the vertex `y` is merged into `x`).

Results:

* `numTrees_split`            : `numTrees = numTreesWith e + numTreesWithout e`;
* `numTreesWithout_le_delete` : `numTreesWithout e ≤ numTrees (G − e)`;
* `numTreesWith_le_contract`  : `numTreesWith f ≤ numTrees (G / f)`;
* `deg_delete`                : the degrees in `G − e`;
* `exists_edge_of_conn`       : a path from `y` to another vertex uses a non-loop edge at `y`;
* `numTrees_le_one`           : at most one spanning tree when `|V| ≤ 1`.
-/

open Finset

namespace Kenyon

open TreeEntropy

variable {V E : Type}

/-- A path from `y` to another vertex uses an edge at `y` that is not a loop. -/
theorem exists_edge_of_conn {src tgt : E → V} {F : Finset E} {y w : V}
    (h : Conn src tgt F y w) (hw : w ≠ y) :
    ∃ f ∈ F, (src f = y ∧ tgt f ≠ y) ∨ (tgt f = y ∧ src f ≠ y) := by
  induction h with
  | refl => exact absurd rfl hw
  | @tail b c _ hbc ih =>
    by_cases hb : b = y
    · obtain ⟨f, hf, h'⟩ := hbc
      refine ⟨f, hf, ?_⟩
      rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.trans hb, by rw [h2]; exact hw⟩
      · exact Or.inr ⟨h2.trans hb, by rw [h1]; exact hw⟩
    · exact ih hb

variable [Fintype V] [Fintype E]

theorem numTrees_le_one (src tgt : E → V) (h : Fintype.card V ≤ 1) : numTrees src tgt ≤ 1 := by
  classical
  unfold numTrees
  have hsub : (univ.filter fun T => IsTree src tgt T) ⊆ ({∅} : Finset (Finset E)) := by
    intro T hT
    rw [Finset.mem_filter] at hT
    have h1 := hT.2.1
    rw [Finset.mem_singleton]
    exact Finset.card_eq_zero.1 (by omega)
  calc _ ≤ ({∅} : Finset (Finset E)).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton _

/-- A spanning tree that contains `e`. -/
def IsTreeWith (src tgt : E → V) (e : E) (T : Finset E) : Prop := IsTree src tgt T ∧ e ∈ T

/-- A spanning tree that does not contain `e`. -/
def IsTreeWithout (src tgt : E → V) (e : E) (T : Finset E) : Prop := IsTree src tgt T ∧ e ∉ T

open scoped Classical in
/-- The number of spanning trees that contain `e`. -/
noncomputable def numTreesWith (src tgt : E → V) (e : E) : ℕ :=
  ((univ : Finset (Finset E)).filter fun T => IsTreeWith src tgt e T).card

open scoped Classical in
/-- The number of spanning trees that do not contain `e`. -/
noncomputable def numTreesWithout (src tgt : E → V) (e : E) : ℕ :=
  ((univ : Finset (Finset E)).filter fun T => IsTreeWithout src tgt e T).card

theorem numTrees_split (src tgt : E → V) (e : E) :
    numTrees src tgt = numTreesWith src tgt e + numTreesWithout src tgt e := by
  classical
  unfold numTrees numTreesWith numTreesWithout
  have h1 : ((univ.filter fun T => IsTree src tgt T).filter fun T => e ∈ T)
      = (univ : Finset (Finset E)).filter fun T => IsTreeWith src tgt e T := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  have h2 : ((univ.filter fun T => IsTree src tgt T).filter fun T => ¬ e ∈ T)
      = (univ : Finset (Finset E)).filter fun T => IsTreeWithout src tgt e T := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  rw [← Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Finset E)).filter fun T => IsTree src tgt T) (p := fun T => e ∈ T),
    h1, h2]

/-- An end map of `G − e`. -/
def dmap (g : E → V) (e : E) (e' : {e' : E // e' ≠ e}) : V := g e'.1

theorem numTreesWithout_le_delete [DecidableEq E] (src tgt : E → V) (e : E) :
    numTreesWithout src tgt e ≤ numTrees (dmap src e) (dmap tgt e) := by
  classical
  unfold numTreesWithout numTrees
  refine Finset.card_le_card_of_injOn (fun T => T.subtype (fun e' => e' ≠ e)) ?_ ?_
  · intro T hT
    rw [Finset.mem_coe, Finset.mem_filter] at hT
    obtain ⟨-, hT, heT⟩ := hT
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [Finset.card_subtype, Finset.filter_ne', Finset.erase_eq_of_notMem heT]
      exact hT.1
    · have hlift : ∀ a b, Conn src tgt T a b →
          Conn (dmap src e) (dmap tgt e) (T.subtype fun e' => e' ≠ e) a b := by
        intro a b hab
        induction hab with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hbc ih =>
          obtain ⟨e', he', h⟩ := hbc
          have hne : e' ≠ e := fun h' => heT (h' ▸ he')
          exact Relation.ReflTransGen.tail ih ⟨⟨e', hne⟩, Finset.mem_subtype.2 he', h⟩
      exact fun a b => hlift a b (hT.2 a b)
  · intro T hT S hS hEq
    rw [Finset.mem_coe, Finset.mem_filter] at hT hS
    simp only at hEq
    ext e'
    by_cases hef : e' = e
    · subst hef
      exact ⟨fun h => absurd h hT.2.2, fun h => absurd h hS.2.2⟩
    · have h1 : (⟨e', hef⟩ : {e' : E // e' ≠ e}) ∈ T.subtype (fun e' => e' ≠ e)
          ↔ (⟨e', hef⟩ : {e' : E // e' ≠ e}) ∈ S.subtype (fun e' => e' ≠ e) := by rw [hEq]
      simpa [Finset.mem_subtype] using h1

variable [DecidableEq V]

/-- The projection of the contraction: `y` goes to `x`. -/
def cproj (x y : V) (hxy : x ≠ y) (v : V) : {v : V // v ≠ y} :=
  if h : v = y then ⟨x, hxy⟩ else ⟨v, h⟩

/-- An end map of `G / f`, where `f` has the ends `x ≠ y`. -/
def cmap (g : E → V) (f : E) (x y : V) (hxy : x ≠ y) (e' : {e' : E // e' ≠ f}) :
    {v : V // v ≠ y} :=
  cproj x y hxy (g e'.1)

theorem numTreesWith_le_contract [DecidableEq E] (src tgt : E → V) (f : E) (x y : V)
    (hxy : x ≠ y)
    (hf : (src f = x ∧ tgt f = y) ∨ (src f = y ∧ tgt f = x)) :
    numTreesWith src tgt f ≤ numTrees (cmap src f x y hxy) (cmap tgt f x y hxy) := by
  classical
  have hx : cproj x y hxy x = ⟨x, hxy⟩ := by simp [cproj, hxy]
  have hy : cproj x y hxy y = ⟨x, hxy⟩ := by simp [cproj]
  unfold numTreesWith numTrees
  refine Finset.card_le_card_of_injOn (fun T => T.subtype (fun e' => e' ≠ f)) ?_ ?_
  · intro T hT
    rw [Finset.mem_coe, Finset.mem_filter] at hT
    obtain ⟨-, hT, hfT⟩ := hT
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [Finset.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem hfT]
      have hV : Fintype.card {v : V // v ≠ y} = Fintype.card V - 1 := by
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      rw [hV]
      have h1 := hT.1
      have h2 := Finset.card_pos.2 ⟨f, hfT⟩
      omega
    · have hlift : ∀ a b, Conn src tgt T a b →
          Conn (cmap src f x y hxy) (cmap tgt f x y hxy) (T.subtype fun e' => e' ≠ f)
            (cproj x y hxy a) (cproj x y hxy b) := by
        intro a b hab
        induction hab with
        | refl => exact Relation.ReflTransGen.refl
        | @tail b c _ hbc ih =>
          obtain ⟨e', he', h⟩ := hbc
          by_cases hef : e' = f
          · subst hef
            have hπ : cproj x y hxy b = cproj x y hxy c := by
              rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hf with ⟨h3, h4⟩ | ⟨h3, h4⟩
              · rw [h1.symm.trans h3, h2.symm.trans h4, hx, hy]
              · rw [h1.symm.trans h3, h2.symm.trans h4, hx, hy]
              · rw [h2.symm.trans h4, h1.symm.trans h3, hx, hy]
              · rw [h2.symm.trans h4, h1.symm.trans h3, hx, hy]
            rw [← hπ]
            exact ih
          · refine Relation.ReflTransGen.tail ih ⟨⟨e', hef⟩, Finset.mem_subtype.2 he', ?_⟩
            rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨by simp [cmap, h1], by simp [cmap, h2]⟩
            · exact Or.inr ⟨by simp [cmap, h1], by simp [cmap, h2]⟩
      intro a b
      have ha : cproj x y hxy a.1 = a := by
        obtain ⟨a, ha⟩ := a
        simp [cproj, ha]
      have hb : cproj x y hxy b.1 = b := by
        obtain ⟨b, hb⟩ := b
        simp [cproj, hb]
      have := hlift a.1 b.1 (hT.2 a.1 b.1)
      rwa [ha, hb] at this
  · intro T hT S hS hEq
    rw [Finset.mem_coe, Finset.mem_filter] at hT hS
    simp only at hEq
    ext e'
    by_cases hef : e' = f
    · subst hef
      exact ⟨fun _ => hS.2.2, fun _ => hT.2.2⟩
    · have h1 : (⟨e', hef⟩ : {e' : E // e' ≠ f}) ∈ T.subtype (fun e' => e' ≠ f)
          ↔ (⟨e', hef⟩ : {e' : E // e' ≠ f}) ∈ S.subtype (fun e' => e' ≠ f) := by rw [hEq]
      simpa [Finset.mem_subtype] using h1

omit [Fintype V] [DecidableEq V] in
theorem card_filter_subtype_ne [DecidableEq E] (e : E) (p : E → Prop) [DecidablePred p] :
    (univ.filter fun e' : {e' : E // e' ≠ e} => p e'.1).card
      = ((univ.filter p).erase e).card := by
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext a
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype, Finset.mem_erase, Subtype.exists, exists_and_right,
    exists_eq_right]
  tauto

omit [Fintype V] in
/-- The degrees in `G − e`. -/
theorem deg_delete [DecidableEq E] (src tgt : E → V) (e : E) (x : V) :
    deg (dmap src e) (dmap tgt e) x
        + ((if src e = x then 1 else 0) + (if tgt e = x then 1 else 0))
      = deg src tgt x := by
  have p1 : src e = x → 0 < (univ.filter fun e' => src e' = x).card := fun h =>
    Finset.card_pos.2 ⟨e, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩
  have p2 : tgt e = x → 0 < (univ.filter fun e' => tgt e' = x).card := fun h =>
    Finset.card_pos.2 ⟨e, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩
  unfold deg dmap
  rw [card_filter_subtype_ne e (fun e' => src e' = x),
    card_filter_subtype_ne e (fun e' => tgt e' = x), Finset.card_erase_eq_ite,
    Finset.card_erase_eq_ite]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h1 : src e = x
  · by_cases h2 : tgt e = x
    · have := p1 h1
      have := p2 h2
      simp only [h1, h2, ite_true]
      omega
    · have := p1 h1
      simp only [h1, h2, ite_true, ite_false]
      omega
  · by_cases h2 : tgt e = x
    · have := p2 h2
      simp only [h1, h2, ite_true, ite_false]
      omega
    · simp only [h1, h2, ite_false]
      omega

end Kenyon
