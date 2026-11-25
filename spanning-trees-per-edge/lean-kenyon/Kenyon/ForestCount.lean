import Kenyon.Forest

/-!
# Counting lemmas for forests (used for the sharpness of the bound)

* `card_le_of_conn`   : if `F` joins every vertex to a vertex of `R`, then `|V| ≤ |R| + |F|`;
* `numForests_ge`     : the reverse of `numForests_le`, so the recursion along an edge with
  exactly one end in `R` is an equality;
* `one_le_numForests_univ` : the empty set is the forest with root set `V`;
* `exists_tree_of_forest`  : in a connected multigraph every rooted spanning forest with a
  nonempty root set is contained in a spanning tree;
* `numForests_le_numTrees_mul` : hence
  `numForests univ R ≤ numTrees · #{S : Finset E | |S| + 1 = |R|}`.
-/

open Finset

namespace Kenyon

variable {V E : Type} {src tgt : E → V}

theorem conn_empty {x y : V} (h : Conn src tgt ∅ x y) : x = y := by
  induction h with
  | refl => rfl
  | tail _ hbc _ =>
    obtain ⟨e, he, -⟩ := hbc
    exact absurd he (Finset.notMem_empty e)

variable [Fintype V]

/-- **Counting lemma.** -/
theorem card_le_of_conn [DecidableEq V] [DecidableEq E] (src tgt : E → V) (F : Finset E) :
    ∀ R : Finset V, (∀ x, ∃ ρ ∈ R, Conn src tgt F x ρ) →
      Fintype.card V ≤ R.card + F.card := by
  induction F using Finset.induction_on with
  | empty =>
    intro R h
    have hsub : (univ : Finset V) ⊆ R := fun x _ => by
      obtain ⟨ρ, hρ, hx⟩ := h x
      rw [conn_empty hx]
      exact hρ
    simpa using Finset.card_le_card hsub
  | insert e F' he ih =>
    intro R h
    have herase : (insert e F').erase e = F' := Finset.erase_insert he
    obtain ⟨ρ0, hρ0, h0⟩ := h (src e)
    have h0' := conn_erase e h0.symm
    rw [herase] at h0'
    have key : ∀ p q : V, ((p = src e ∧ q = tgt e) ∨ (p = tgt e ∧ q = src e)) →
        Conn src tgt F' ρ0 p → Fintype.card V ≤ R.card + (insert e F').card := by
      intro p q hpq hp
      have hall : ∀ x, ∃ ρ ∈ insert q R, Conn src tgt F' x ρ := by
        intro x
        obtain ⟨ρ1, hρ1, h1⟩ := h x
        have h1' := conn_erase e h1
        rw [herase] at h1'
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases h1' with h1' | h1' | h1'
          · exact ⟨ρ1, Finset.mem_insert_of_mem hρ1, h1'⟩
          · exact ⟨ρ0, Finset.mem_insert_of_mem hρ0, h1'.trans hp.symm⟩
          · exact ⟨tgt e, Finset.mem_insert_self _ _, h1'⟩
        · rcases h1' with h1' | h1' | h1'
          · exact ⟨ρ1, Finset.mem_insert_of_mem hρ1, h1'⟩
          · exact ⟨src e, Finset.mem_insert_self _ _, h1'⟩
          · exact ⟨ρ0, Finset.mem_insert_of_mem hρ0, h1'.trans hp.symm⟩
      have h2 := ih (insert q R) hall
      have c1 := Finset.card_insert_le q R
      rw [Finset.card_insert_of_notMem he]
      omega
    rcases h0' with h0' | h0' | h0'
    · exact key (src e) (tgt e) (Or.inl ⟨rfl, rfl⟩) h0'
    · exact key (src e) (tgt e) (Or.inl ⟨rfl, rfl⟩) h0'
    · exact key (tgt e) (src e) (Or.inr ⟨rfl, rfl⟩) h0'

/-- Adding to a forest with root set `R ∪ {u}` an edge from `u` to `R` gives a forest with root
set `R`. -/
theorem IsForest.insertEdge [DecidableEq E] [DecidableEq V] {R : Finset V} {F : Finset E}
    {u : V} (hF : IsForest src tgt (insert u R) F) {e : E} (he : e ∉ F) (hu : u ∉ R)
    (hc : (src e = u ∧ tgt e ∈ R) ∨ (tgt e = u ∧ src e ∈ R)) :
    IsForest src tgt R (insert e F) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [Finset.card_insert_of_notMem he]
    have h := hF.1
    rw [Finset.card_insert_of_notMem hu] at h
    omega
  · obtain ⟨ρ, hρ, hx⟩ := hF.2 x
    have hx' : Conn src tgt (insert e F) x ρ := hx.mono (Finset.subset_insert e F)
    have hstep : Conn src tgt (insert e F) (src e) (tgt e) :=
      Conn.step (Finset.mem_insert_self e F)
    rcases Finset.mem_insert.1 hρ with hρu | hρ
    · rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨tgt e, h2, hx'.trans ?_⟩
        rw [hρu, ← h1]
        exact hstep
      · refine ⟨src e, h2, hx'.trans ?_⟩
        rw [hρu, ← h1]
        exact hstep.symm
    · exact ⟨ρ, hρ, hx'⟩

/-- **Recursion along an edge with exactly one end in `R`**, the reverse inequality. -/
theorem numForests_ge [DecidableEq E] [DecidableEq V] (src tgt : E → V) {Es : Finset E}
    {R : Finset V} {e : E} (he : e ∈ Es) {u : V} (hu : u ∉ R)
    (hc : (src e = u ∧ tgt e ∈ R) ∨ (tgt e = u ∧ src e ∈ R)) :
    numForests src tgt (Es.erase e) R + numForests src tgt (Es.erase e) (insert u R)
      ≤ numForests src tgt Es R := by
  classical
  unfold numForests
  set B := Es.powerset.filter fun F => IsForest src tgt R F with hB
  have h0 : ((Es.erase e).powerset.filter fun F => IsForest src tgt R F)
      ⊆ B.filter (fun F => e ∉ F) := by
    intro F hF
    rw [Finset.mem_filter, Finset.mem_powerset] at hF
    rw [Finset.mem_filter, hB, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨⟨hF.1.trans (Finset.erase_subset e Es), hF.2⟩,
      fun h => (Finset.mem_erase.1 (hF.1 h)).1 rfl⟩
  have h1 : ((Es.erase e).powerset.filter fun F => IsForest src tgt (insert u R) F).card
      ≤ (B.filter fun F => ¬ e ∉ F).card := by
    refine Finset.card_le_card_of_injOn (fun F => insert e F) ?_ ?_
    · intro F hF
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hF
      have heF : e ∉ F := fun h => (Finset.mem_erase.1 (hF.1 h)).1 rfl
      rw [Finset.mem_coe, Finset.mem_filter, hB, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨⟨Finset.insert_subset he (hF.1.trans (Finset.erase_subset e Es)),
        hF.2.insertEdge heF hu hc⟩, not_not.2 (Finset.mem_insert_self e F)⟩
    · intro F hF F' hF' hEq
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hF hF'
      have heF : e ∉ F := fun h => (Finset.mem_erase.1 (hF.1 h)).1 rfl
      have heF' : e ∉ F' := fun h => (Finset.mem_erase.1 (hF'.1 h)).1 rfl
      simp only at hEq
      have h2 : (insert e F).erase e = (insert e F').erase e := by rw [hEq]
      rwa [Finset.erase_insert heF, Finset.erase_insert heF'] at h2
  have hsplit := Finset.card_filter_add_card_filter_not (s := B) (p := fun F => e ∉ F)
  have h3 := Finset.card_le_card h0
  omega

theorem one_le_numForests_univ (src tgt : E → V) (Es : Finset E) :
    1 ≤ numForests src tgt Es univ := by
  classical
  unfold numForests
  apply Finset.card_pos.2
  refine ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, ?_, fun x => ?_⟩⟩
  · simp
  · exact ⟨x, Finset.mem_univ x, Conn.refl⟩

/-- **Extension.** In a connected multigraph a rooted spanning forest with a nonempty root set
is contained in a spanning tree. -/
theorem exists_tree_of_forest [Fintype E] [DecidableEq V] [DecidableEq E] (src tgt : E → V)
    (hconn : ∀ x y, Conn src tgt univ x y) :
    ∀ (k : ℕ) (R : Finset V) (F : Finset E), R.card = k + 1 → IsForest src tgt R F →
      ∃ T, IsTree src tgt T ∧ F ⊆ T := by
  classical
  intro k
  induction k with
  | zero =>
    intro R F hR hF
    obtain ⟨r, rfl⟩ := Finset.card_eq_one.1 hR
    refine ⟨F, ⟨by simpa using hF.1, fun x y => ?_⟩, Finset.Subset.refl F⟩
    obtain ⟨ρ, hρ, hx⟩ := hF.2 x
    obtain ⟨ρ', hρ', hy⟩ := hF.2 y
    rw [Finset.mem_singleton] at hρ hρ'
    rw [hρ] at hx
    rw [hρ'] at hy
    exact hx.trans hy.symm
  | succ k ih =>
    intro R F hR hF
    obtain ⟨ρ1, hρ1⟩ : R.Nonempty := Finset.card_pos.1 (by omega)
    -- a vertex not joined to ρ1
    obtain ⟨x, hx⟩ : ∃ x, ¬ Conn src tgt F x ρ1 := by
      by_contra h
      have hall : ∀ x, ∃ ρ ∈ ({ρ1} : Finset V), Conn src tgt F x ρ := fun x =>
        ⟨ρ1, Finset.mem_singleton_self ρ1, by_contra fun hx => h ⟨x, hx⟩⟩
      have h1 := card_le_of_conn src tgt F {ρ1} hall
      have h2 := hF.1
      simp only [Finset.card_singleton] at h1
      omega
    set C : Finset V := univ.filter fun v => Conn src tgt F v ρ1 with hC
    have hxC : x ∉ C := fun h => hx (Finset.mem_filter.1 h).2
    have hρC : ρ1 ∈ C := Finset.mem_filter.2 ⟨Finset.mem_univ _, Conn.refl⟩
    obtain ⟨e, -, he⟩ := exists_crossing (hconn x ρ1) hxC hρC
    -- the outer end `w` and the inner end `u`
    obtain ⟨w, u, hw, hu, hwu⟩ : ∃ w u, w ∉ C ∧ u ∈ C
        ∧ ((src e = w ∧ tgt e = u) ∨ (src e = u ∧ tgt e = w)) := by
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨src e, tgt e, h1, h2, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨tgt e, src e, h1, h2, Or.inr ⟨rfl, rfl⟩⟩
    have huρ : Conn src tgt F u ρ1 := (Finset.mem_filter.1 hu).2
    have hwρ : ¬ Conn src tgt F w ρ1 := fun h => hw (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    have heF : e ∉ F := by
      intro h
      apply hwρ
      have hstep : Conn src tgt F w u := Relation.ReflTransGen.single ⟨e, h, hwu⟩
      exact hstep.trans huρ
    obtain ⟨ρ', hρ', hwρ'⟩ := hF.2 w
    have hne : ρ1 ≠ ρ' := fun h => hwρ (h ▸ hwρ')
    have hF' : IsForest src tgt (R.erase ρ') (insert e F) := by
      refine ⟨?_, fun y => ?_⟩
      · rw [Finset.card_insert_of_notMem heF, Finset.card_erase_of_mem hρ']
        have := hF.1
        omega
      · obtain ⟨ρ, hρ, hy⟩ := hF.2 y
        have hy' : Conn src tgt (insert e F) y ρ := hy.mono (Finset.subset_insert e F)
        by_cases hρρ : ρ = ρ'
        · refine ⟨ρ1, Finset.mem_erase.2 ⟨hne, hρ1⟩, ?_⟩
          have s1 : Conn src tgt (insert e F) ρ w := by
            rw [hρρ]
            exact (hwρ'.mono (Finset.subset_insert e F)).symm
          have s2 : Conn src tgt (insert e F) w u :=
            Relation.ReflTransGen.single ⟨e, Finset.mem_insert_self e F, hwu⟩
          have s3 : Conn src tgt (insert e F) u ρ1 := huρ.mono (Finset.subset_insert e F)
          exact ((hy'.trans s1).trans s2).trans s3
        · exact ⟨ρ, Finset.mem_erase.2 ⟨hρρ, hρ⟩, hy'⟩
    have hcard : (R.erase ρ').card = k + 1 := by
      rw [Finset.card_erase_of_mem hρ']
      omega
    obtain ⟨T, hT, hsub⟩ := ih (R.erase ρ') (insert e F) hcard hF'
    exact ⟨T, hT, (Finset.subset_insert e F).trans hsub⟩

/-- In a connected multigraph the number of forests with a nonempty root set `R` is at most
the number of spanning trees times the number of sets of `|R| − 1` edges. -/
theorem numForests_le_numTrees_mul [Fintype E] [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (hconn : ∀ x y, Conn src tgt univ x y) {R : Finset V}
    (hR : R.Nonempty) :
    numForests src tgt univ R
      ≤ numTrees src tgt * ((univ : Finset (Finset E)).filter fun S => S.card + 1 = R.card).card := by
  classical
  have hk : R.card = (R.card - 1) + 1 := by
    have := Finset.card_pos.2 hR
    omega
  have hext : ∀ F, IsForest src tgt R F → ∃ T, IsTree src tgt T ∧ F ⊆ T :=
    fun F hF => exists_tree_of_forest src tgt hconn (R.card - 1) R F hk hF
  let g : Finset E → Finset E := fun F =>
    if h : IsForest src tgt R F then Classical.choose (hext F h) else ∅
  have hg : ∀ F (h : IsForest src tgt R F), IsTree src tgt (g F) ∧ F ⊆ g F := by
    intro F h
    simp only [g, h, ↓reduceDIte]
    exact Classical.choose_spec (hext F h)
  unfold numForests numTrees
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun F => (g F, g F \ F)) ?_ ?_
  · intro F hF
    rw [Finset.mem_coe, Finset.mem_filter] at hF
    obtain ⟨hT, hsub⟩ := hg F hF.2
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, hT⟩, Finset.mem_univ _, ?_⟩
    rw [Finset.card_sdiff_of_subset hsub]
    have h1 := hT.1
    have h2 := hF.2.1
    have h3 := Finset.card_le_card hsub
    omega
  · intro F hF F' hF' hEq
    rw [Finset.mem_coe, Finset.mem_filter] at hF hF'
    obtain ⟨-, hsub⟩ := hg F hF.2
    obtain ⟨-, hsub'⟩ := hg F' hF'.2
    simp only [Prod.mk.injEq] at hEq
    obtain ⟨e1, e2⟩ := hEq
    have a1 : g F \ (g F \ F) = F := Finset.sdiff_sdiff_eq_self hsub
    have a2 : g F' \ (g F' \ F') = F' := Finset.sdiff_sdiff_eq_self hsub'
    rw [← a1, ← a2, e2, e1]

end Kenyon
