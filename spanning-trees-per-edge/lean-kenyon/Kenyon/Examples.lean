import Kenyon.Forest

/-!
# Two examples

A check that `numTrees` counts what it should on two small multigraphs:

* `numTrees_loop`  : one vertex with one loop has exactly one spanning tree (the empty set);
* `numTrees_digon` : two vertices joined by two parallel edges have exactly two spanning trees.
-/

open Finset

namespace Kenyon

theorem numTrees_loop : numTrees (fun _ : Unit => ()) (fun _ : Unit => ()) = 1 := by
  classical
  unfold numTrees
  have h : ((univ : Finset (Finset Unit)).filter
      fun T => IsTree (fun _ : Unit => ()) (fun _ : Unit => ()) T) = {∅} := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hT
      have h1 := hT.1
      rw [Fintype.card_unit] at h1
      exact Finset.card_eq_zero.1 (by omega)
    · rintro rfl
      exact ⟨by simp, fun x y => by cases x; cases y; exact Relation.ReflTransGen.refl⟩
  rw [h, Finset.card_singleton]

theorem numTrees_digon :
    numTrees (fun _ : Fin 2 => (0 : Fin 2)) (fun _ : Fin 2 => (1 : Fin 2)) = 2 := by
  classical
  unfold numTrees
  have h : ((univ : Finset (Finset (Fin 2))).filter
      fun T => IsTree (fun _ : Fin 2 => (0 : Fin 2)) (fun _ : Fin 2 => (1 : Fin 2)) T)
      = Finset.powersetCard 1 univ := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
      Finset.subset_univ]
    constructor
    · intro hT
      have h1 := hT.1
      rw [Fintype.card_fin] at h1
      omega
    · intro hT
      obtain ⟨e, rfl⟩ := Finset.card_eq_one.1 hT
      have h01 : Conn (fun _ : Fin 2 => (0 : Fin 2)) (fun _ : Fin 2 => (1 : Fin 2)) {e} 0 1 :=
        Relation.ReflTransGen.single ⟨e, Finset.mem_singleton_self e, Or.inl ⟨rfl, rfl⟩⟩
      refine ⟨by simp, fun x y => ?_⟩
      fin_cases x <;> fin_cases y
      · exact Relation.ReflTransGen.refl
      · exact h01
      · exact h01.symm
      · exact Relation.ReflTransGen.refl
  rw [h, Finset.card_powersetCard]
  simp

end Kenyon
