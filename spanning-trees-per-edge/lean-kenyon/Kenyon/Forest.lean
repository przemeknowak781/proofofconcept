import Mathlib

/-!
# Spanning trees and rooted spanning forests of a multigraph

A multigraph is given by two maps `src tgt : E → V`. A set of edges `F : Finset E` joins `x`
and `y` (`Conn src tgt F x y`) if there is a path from `x` to `y` whose edges lie in `F`.

* `IsTree src tgt T`     : `|T| + 1 = |V|` and `T` joins every two vertices (a spanning tree);
* `IsForest src tgt R F` : `|F| + |R| = |V|` and `F` joins every vertex to a vertex of `R`
  (a spanning forest with exactly one root in each component, the roots being `R`);
* `numTrees src tgt`, `numForests src tgt Es R` (forests contained in `Es`).

Results:

* `numTrees_le_numForests` : `numTrees ≤ numForests univ {r}`;
* `numForests_univ_le`     : `numForests Es univ ≤ 1`;
* `numForests_le`          : for an edge `e ∈ Es` with one end `u ∉ R` and the other end in `R`,
  `numForests Es R ≤ numForests (Es − e) R + numForests (Es − e) (R ∪ {u})`;
* `numForests_eq_zero`     : if `R ≠ V` and no edge of `Es` has exactly one end in `R`, then
  `numForests Es R = 0`.
-/

open Finset

namespace Kenyon

variable {V E : Type}

/-- `x` and `y` are the two ends of an edge of `F`. -/
def Adj (src tgt : E → V) (F : Finset E) (x y : V) : Prop :=
  ∃ e ∈ F, (src e = x ∧ tgt e = y) ∨ (src e = y ∧ tgt e = x)

/-- `x` and `y` are joined by a path with edges in `F`. -/
def Conn (src tgt : E → V) (F : Finset E) : V → V → Prop :=
  Relation.ReflTransGen (Adj src tgt F)

/-- A spanning forest with root set `R`. -/
def IsForest [Fintype V] (src tgt : E → V) (R : Finset V) (F : Finset E) : Prop :=
  F.card + R.card = Fintype.card V ∧ ∀ x, ∃ ρ ∈ R, Conn src tgt F x ρ

/-- A spanning tree. -/
def IsTree [Fintype V] (src tgt : E → V) (T : Finset E) : Prop :=
  T.card + 1 = Fintype.card V ∧ ∀ x y, Conn src tgt T x y

open scoped Classical in
/-- The number of spanning trees. -/
noncomputable def numTrees [Fintype V] [Fintype E] (src tgt : E → V) : ℕ :=
  ((univ : Finset (Finset E)).filter fun T => IsTree src tgt T).card

open scoped Classical in
/-- The number of spanning forests with root set `R` contained in `Es`. -/
noncomputable def numForests [Fintype V] (src tgt : E → V) (Es : Finset E) (R : Finset V) : ℕ :=
  (Es.powerset.filter fun F => IsForest src tgt R F).card

section Basic

variable {src tgt : E → V} {F F' : Finset E} {x y z : V}

theorem Adj.symm (h : Adj src tgt F x y) : Adj src tgt F y x := by
  obtain ⟨e, he, h⟩ := h
  exact ⟨e, he, h.symm⟩

theorem Conn.refl : Conn src tgt F x x := Relation.ReflTransGen.refl

theorem Conn.symm (h : Conn src tgt F x y) : Conn src tgt F y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head hbc.symm ih

theorem Conn.trans (h1 : Conn src tgt F x y) (h2 : Conn src tgt F y z) : Conn src tgt F x z :=
  Relation.ReflTransGen.trans h1 h2

theorem Conn.mono (hF : F ⊆ F') (h : Conn src tgt F x y) : Conn src tgt F' x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    obtain ⟨e, he, h'⟩ := hbc
    exact Relation.ReflTransGen.tail ih ⟨e, hF he, h'⟩

theorem Conn.step {e : E} (he : e ∈ F) : Conn src tgt F (src e) (tgt e) :=
  Relation.ReflTransGen.single ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩

/-- A path in `F` avoids `e`, or it reaches an end of `e` without using `e`. -/
theorem conn_erase [DecidableEq E] (e : E) (h : Conn src tgt F x y) :
    Conn src tgt (F.erase e) x y ∨ Conn src tgt (F.erase e) x (src e)
      ∨ Conn src tgt (F.erase e) x (tgt e) := by
  induction h with
  | refl => exact Or.inl Conn.refl
  | tail _ hbc ih =>
    rcases ih with ih | ih
    · obtain ⟨e', he', h'⟩ := hbc
      by_cases hee : e' = e
      · subst hee
        rcases h' with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact Or.inr (Or.inl (h1 ▸ ih))
        · exact Or.inr (Or.inr (h2 ▸ ih))
      · exact Or.inl (Relation.ReflTransGen.tail ih
          ⟨e', Finset.mem_erase.2 ⟨hee, he'⟩, h'⟩)
    · exact Or.inr ih

/-- A path from outside `R` into `R` uses an edge with exactly one end in `R`. -/
theorem exists_crossing {R : Finset V} (h : Conn src tgt F x y) (hx : x ∉ R) (hy : y ∈ R) :
    ∃ e ∈ F, (src e ∉ R ∧ tgt e ∈ R) ∨ (tgt e ∉ R ∧ src e ∈ R) := by
  induction h with
  | refl => exact absurd hy hx
  | @tail b c _ hbc ih =>
    by_cases hb : b ∈ R
    · exact ih hb
    · obtain ⟨e, he, h'⟩ := hbc
      refine ⟨e, he, ?_⟩
      rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1 ▸ hb, h2 ▸ hy⟩
      · exact Or.inr ⟨h2 ▸ hb, h1 ▸ hy⟩

end Basic

section Count

variable [Fintype V] {src tgt : E → V}

theorem IsTree.isForest {T : Finset E} (h : IsTree src tgt T) (r : V) :
    IsForest src tgt {r} T :=
  ⟨by simpa using h.1, fun x => ⟨r, Finset.mem_singleton_self r, h.2 x r⟩⟩

theorem numTrees_le_numForests [Fintype E] (src tgt : E → V) (r : V) :
    numTrees src tgt ≤ numForests src tgt univ {r} := by
  classical
  unfold numTrees numForests
  refine Finset.card_le_card fun T hT => ?_
  rw [Finset.mem_filter] at hT ⊢
  exact ⟨Finset.mem_powerset.2 (Finset.subset_univ _), hT.2.isForest r⟩

theorem numForests_univ_le (src tgt : E → V) (Es : Finset E) :
    numForests src tgt Es univ ≤ 1 := by
  classical
  unfold numForests
  have : (Es.powerset.filter fun F => IsForest src tgt univ F) ⊆ {∅} := by
    intro F hF
    rw [Finset.mem_filter] at hF
    have h := hF.2.1
    rw [Finset.card_univ] at h
    have : F.card = 0 := by omega
    rw [Finset.mem_singleton]
    exact Finset.card_eq_zero.1 this
  calc _ ≤ ({∅} : Finset (Finset E)).card := Finset.card_le_card this
    _ = 1 := Finset.card_singleton _

/-- Removing from a forest an edge with one end `u ∉ R` and the other end in `R` gives a forest
with root set `R ∪ {u}`. -/
theorem IsForest.erase [DecidableEq E] [DecidableEq V] {R : Finset V} {F : Finset E}
    (hF : IsForest src tgt R F) {e : E} (he : e ∈ F) {u : V} (hu : u ∉ R)
    (hc : (src e = u ∧ tgt e ∈ R) ∨ (tgt e = u ∧ src e ∈ R)) :
    IsForest src tgt (insert u R) (F.erase e) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [Finset.card_erase_of_mem he, Finset.card_insert_of_notMem hu]
    have := hF.1
    have hpos : 0 < F.card := Finset.card_pos.2 ⟨e, he⟩
    omega
  · obtain ⟨ρ, hρ, hx⟩ := hF.2 x
    rcases conn_erase e hx with h | h | h
    · exact ⟨ρ, Finset.mem_insert_of_mem hρ, h⟩
    · rcases hc with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact ⟨u, Finset.mem_insert_self u R, h1 ▸ h⟩
      · exact ⟨src e, Finset.mem_insert_of_mem h2, h⟩
    · rcases hc with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact ⟨tgt e, Finset.mem_insert_of_mem h2, h⟩
      · exact ⟨u, Finset.mem_insert_self u R, h1 ▸ h⟩

/-- **Recursion along an edge with exactly one end in `R`** (inequality). -/
theorem numForests_le [DecidableEq E] [DecidableEq V] (src tgt : E → V) {Es : Finset E}
    {R : Finset V} {e : E} {u : V} (hu : u ∉ R)
    (hc : (src e = u ∧ tgt e ∈ R) ∨ (tgt e = u ∧ src e ∈ R)) :
    numForests src tgt Es R
      ≤ numForests src tgt (Es.erase e) R + numForests src tgt (Es.erase e) (insert u R) := by
  classical
  unfold numForests
  set A := Es.powerset.filter fun F => IsForest src tgt R F with hA
  have hsplit : A.card = (A.filter fun F => e ∉ F).card + (A.filter fun F => ¬ e ∉ F).card :=
    (Finset.card_filter_add_card_filter_not (s := A) (p := fun F => e ∉ F)).symm
  have h0 : (A.filter fun F => e ∉ F).card
      ≤ ((Es.erase e).powerset.filter fun F => IsForest src tgt R F).card := by
    refine Finset.card_le_card fun F hF => ?_
    rw [Finset.mem_filter, hA, Finset.mem_filter, Finset.mem_powerset] at hF
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_erase.2 ⟨hF.1.1, hF.2⟩, hF.1.2⟩
  have h1 : (A.filter fun F => ¬ e ∉ F).card
      ≤ ((Es.erase e).powerset.filter fun F => IsForest src tgt (insert u R) F).card := by
    refine Finset.card_le_card_of_injOn (fun F => F.erase e) ?_ ?_
    · intro F hF
      rw [Finset.mem_coe, Finset.mem_filter, hA, Finset.mem_filter, Finset.mem_powerset] at hF
      have heF : e ∈ F := not_not.1 hF.2
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.erase_subset_erase e hF.1.1, hF.1.2.erase heF hu hc⟩
    · intro F hF F' hF' hEq
      rw [Finset.mem_coe, Finset.mem_filter] at hF hF'
      have heF : e ∈ F := not_not.1 hF.2
      have heF' : e ∈ F' := not_not.1 hF'.2
      have : insert e (F.erase e) = insert e (F'.erase e) := by
        simp only at hEq
        rw [hEq]
      rwa [Finset.insert_erase heF, Finset.insert_erase heF'] at this
  omega

/-- No edge with exactly one end in `R`, and `R ≠ V`: no forest. -/
theorem numForests_eq_zero (src tgt : E → V) {Es : Finset E} {R : Finset V} {x : V}
    (hx : x ∉ R)
    (hno : ¬ ∃ e ∈ Es, (src e ∉ R ∧ tgt e ∈ R) ∨ (tgt e ∉ R ∧ src e ∈ R)) :
    numForests src tgt Es R = 0 := by
  classical
  unfold numForests
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro F hF hforest
  obtain ⟨ρ, hρ, hconn⟩ := hforest.2 x
  obtain ⟨e, he, h⟩ := exists_crossing hconn hx hρ
  exact hno ⟨e, Finset.mem_powerset.1 hF he, h⟩

end Count

end Kenyon
