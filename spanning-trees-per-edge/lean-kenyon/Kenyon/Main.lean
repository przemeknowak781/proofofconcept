import Kenyon.Amplify
import Kenyon.Contract

/-!
# The universal bound

`kenyon_bound`: for every finite multigraph `src tgt : E → V` (loops and multiple edges
allowed, no further hypothesis) with `m = |E| ≥ 1` edges, the number `τ` of spanning trees
satisfies

    τ² · 8^m < 27^m,          that is,          τ < (27/8)^(m/2)

(`kenyon_bound_real`).

Proof of `numTrees_le_pow` (`τ ≤ c^m` with `c = √(27/8)`), by strong induction on `m`:

* `|V| ≤ 1`: `τ ≤ 1`;
* a vertex without a non-loop edge (in particular of degree `0`, or of degree `2` with a loop):
  `τ = 0`;
* a vertex of degree `1` (`pendant_step`): every spanning tree contains its edge `f`, so
  `τ(G) ≤ τ(G / f) ≤ c^(m−1)`;
* every degree at least `2` and no edge joining two vertices of degree `2`: the analytic bound
  `numTrees_le_exp_classC`;
* an edge `e` (not a loop) joining two vertices of degree `2`:
  `τ(G) ≤ τ(G / e) + τ(G − e)`, the graph `G − e` has a vertex of degree `1`, hence
  `τ(G) ≤ c^(m−1) + c^(m−2) ≤ c^m` because `c + 1 ≤ c²`.

The strict inequality follows from parity: `τ² · 8^m` is even and `27^m` is odd.
-/

open Finset

namespace Kenyon

open TreeEntropy

/-- `c = √(27/8)`. -/
noncomputable def cK : ℝ := Real.exp (1 / 2 * Real.log (27 / 8))

theorem cK_pos : 0 < cK := Real.exp_pos _

theorem cK_sq : cK ^ 2 = 27 / 8 := by
  unfold cK
  rw [← Real.exp_natCast_mul]
  have : ((2:ℕ):ℝ) * (1 / 2 * Real.log (27 / 8)) = Real.log (27 / 8) := by
    push_cast
    ring
  rw [this, Real.exp_log (by norm_num)]

theorem one_le_cK : 1 ≤ cK := by
  nlinarith [cK_sq, cK_pos]

theorem cK_add_one_le : cK + 1 ≤ cK ^ 2 := by
  have h : cK ≤ 19 / 8 := by nlinarith [cK_sq, cK_pos]
  rw [cK_sq]
  linarith

/-- The step for a vertex of degree `1`. -/
theorem pendant_step (m : ℕ)
    (IH : ∀ m' < m, ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] (src tgt : E → V),
      Fintype.card E = m' → (numTrees src tgt : ℝ) ≤ cK ^ m')
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] (src tgt : E → V)
    (hE : Fintype.card E = m) (y : V) (hy : deg src tgt y = 1) :
    (numTrees src tgt : ℝ) ≤ cK ^ (m - 1) := by
  classical
  obtain ⟨f, x, hxy, hf, huniq⟩ : ∃ f x, x ≠ y
      ∧ ((src f = x ∧ tgt f = y) ∨ (src f = y ∧ tgt f = x))
      ∧ ∀ f', (src f' = y ∨ tgt f' = y) → f' = f := by
    unfold deg at hy
    have hcases : ((univ.filter fun e => src e = y).card = 1
          ∧ (univ.filter fun e => tgt e = y).card = 0)
        ∨ ((univ.filter fun e => src e = y).card = 0
          ∧ (univ.filter fun e => tgt e = y).card = 1) := by omega
    rcases hcases with ⟨h1, h0⟩ | ⟨h0, h1⟩
    · obtain ⟨f, hf⟩ := Finset.card_eq_one.1 h1
      have hfm : f ∈ univ.filter (fun e => src e = y) := by
        rw [hf]
        exact Finset.mem_singleton_self f
      have hsf : src f = y := (Finset.mem_filter.1 hfm).2
      have hempty : ∀ f', tgt f' ≠ y := by
        intro f' h'
        have : f' ∈ univ.filter (fun e => tgt e = y) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, h'⟩
        rw [Finset.card_eq_zero.1 h0] at this
        exact absurd this (Finset.notMem_empty _)
      refine ⟨f, tgt f, hempty f, Or.inr ⟨hsf, rfl⟩, ?_⟩
      intro f' h'
      rcases h' with h' | h'
      · have : f' ∈ univ.filter (fun e => src e = y) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, h'⟩
        rw [hf] at this
        exact Finset.mem_singleton.1 this
      · exact absurd h' (hempty f')
    · obtain ⟨f, hf⟩ := Finset.card_eq_one.1 h1
      have hfm : f ∈ univ.filter (fun e => tgt e = y) := by
        rw [hf]
        exact Finset.mem_singleton_self f
      have htf : tgt f = y := (Finset.mem_filter.1 hfm).2
      have hempty : ∀ f', src f' ≠ y := by
        intro f' h'
        have : f' ∈ univ.filter (fun e => src e = y) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, h'⟩
        rw [Finset.card_eq_zero.1 h0] at this
        exact absurd this (Finset.notMem_empty _)
      refine ⟨f, src f, hempty f, Or.inl ⟨rfl, htf⟩, ?_⟩
      intro f' h'
      rcases h' with h' | h'
      · exact absurd h' (hempty f')
      · have : f' ∈ univ.filter (fun e => tgt e = y) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, h'⟩
        rw [hf] at this
        exact Finset.mem_singleton.1 this
  have hall : numTreesWithout src tgt f = 0 := by
    unfold numTreesWithout
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro T - ⟨hT, hfT⟩
    obtain ⟨f', hf', h'⟩ := exists_edge_of_conn (hT.2 y x) hxy
    have : f' = f := huniq f' (h'.imp (fun h => h.1) (fun h => h.1))
    exact hfT (this ▸ hf')
  have hsplit := numTrees_split src tgt f
  have hle := numTreesWith_le_contract src tgt f x y hxy hf
  have hcardE : Fintype.card {e' : E // e' ≠ f} = m - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hE]
  have hm : 0 < m := by
    rw [← hE]
    exact Fintype.card_pos_iff.2 ⟨f⟩
  have hIH := IH (m - 1) (by omega) _ _ (cmap src f x y hxy) (cmap tgt f x y hxy) hcardE
  have h2 : (numTrees src tgt : ℝ) ≤ numTrees (cmap src f x y hxy) (cmap tgt f x y hxy) := by
    exact_mod_cast (by omega :
      numTrees src tgt ≤ numTrees (cmap src f x y hxy) (cmap tgt f x y hxy))
  linarith

/-- **`τ ≤ c^m` for every finite multigraph.** -/
theorem numTrees_le_pow : ∀ (m : ℕ) (V E : Type) [Fintype V] [Fintype E] [DecidableEq V]
    (src tgt : E → V), Fintype.card E = m → (numTrees src tgt : ℝ) ≤ cK ^ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro V E _ _ _ src tgt hE
    classical
    have hc1 : (1:ℝ) ≤ cK := one_le_cK
    have hpow1 : (1:ℝ) ≤ cK ^ m := one_le_pow₀ hc1
    by_cases hn : Fintype.card V ≤ 1
    · have h := numTrees_le_one src tgt hn
      have : (numTrees src tgt : ℝ) ≤ 1 := by exact_mod_cast h
      linarith
    have hn2 : 2 ≤ Fintype.card V := by omega
    -- a vertex without a non-loop edge: no spanning tree
    have hzero : ∀ y : V,
        (∀ f, ¬((src f = y ∧ tgt f ≠ y) ∨ (tgt f = y ∧ src f ≠ y))) →
        (numTrees src tgt : ℝ) ≤ cK ^ m := by
      intro y hy
      have h0 : numTrees src tgt = 0 := by
        unfold numTrees
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro T _ hT
        obtain ⟨w, hw⟩ : ∃ w, w ≠ y := by
          by_contra h
          have hall : ∀ w, w = y := fun w => by_contra fun hw => h ⟨w, hw⟩
          have : Fintype.card V ≤ 1 :=
            Fintype.card_le_one_iff.2 fun a b => (hall a).trans (hall b).symm
          omega
        obtain ⟨f, -, hf⟩ := exists_edge_of_conn (hT.2 y w) hw
        exact hy f hf
      rw [h0]
      simp only [Nat.cast_zero]
      positivity
    by_cases h0 : ∃ v, deg src tgt v = 0
    · obtain ⟨v, hv⟩ := h0
      apply hzero v
      intro f hf
      unfold deg at hv
      rcases hf with ⟨h, -⟩ | ⟨h, -⟩
      · have : f ∈ univ.filter (fun e => src e = v) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
        have := Finset.card_pos.2 ⟨f, this⟩
        omega
      · have : f ∈ univ.filter (fun e => tgt e = v) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
        have := Finset.card_pos.2 ⟨f, this⟩
        omega
    by_cases h1 : ∃ v, deg src tgt v = 1
    · obtain ⟨v, hv⟩ := h1
      have h := pendant_step m IH src tgt hE v hv
      have hle : cK ^ (m - 1) ≤ cK ^ m := pow_le_pow_right₀ hc1 (Nat.sub_le m 1)
      linarith
    have hdeg : ∀ v, 2 ≤ deg src tgt v := by
      intro v
      have a : deg src tgt v ≠ 0 := fun h => h0 ⟨v, h⟩
      have b : deg src tgt v ≠ 1 := fun h => h1 ⟨v, h⟩
      omega
    by_cases hD : ∀ e, ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2)
    · obtain ⟨r⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
      have h := numTrees_le_exp_classC hdeg hD r
      rw [← hE]
      unfold cK
      rw [← Real.exp_natCast_mul]
      exact h
    obtain ⟨e, hex, hey⟩ : ∃ e, deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2 := by
      by_contra h
      exact hD fun e he => h ⟨e, he⟩
    by_cases hloop : src e = tgt e
    · -- a loop at a vertex of degree 2
      apply hzero (src e)
      intro f hf
      unfold deg at hex
      have m1 : e ∈ univ.filter (fun e' => src e' = src e) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
      have m2 : e ∈ univ.filter (fun e' => tgt e' = src e) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hloop.symm⟩
      have c1 := Finset.card_pos.2 ⟨e, m1⟩
      have c2 := Finset.card_pos.2 ⟨e, m2⟩
      rcases hf with ⟨h, hne⟩ | ⟨h, hne⟩
      · have mf : f ∈ univ.filter (fun e' => src e' = src e) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
        have hc : (univ.filter fun e' => src e' = src e).card ≤ 1 := by omega
        have hfe : f = e := Finset.card_le_one.1 hc f mf e m1
        exact hne (hfe ▸ hloop.symm)
      · have mf : f ∈ univ.filter (fun e' => tgt e' = src e) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
        have hc : (univ.filter fun e' => tgt e' = src e).card ≤ 1 := by omega
        have hfe : f = e := Finset.card_le_one.1 hc f mf e m2
        exact hne (hfe ▸ rfl)
    · -- an edge, not a loop, joining two vertices of degree 2
      have hsplit := numTrees_split src tgt e
      have hc := numTreesWith_le_contract src tgt e (src e) (tgt e) hloop (Or.inl ⟨rfl, rfl⟩)
      have hd := numTreesWithout_le_delete src tgt e
      have hcardE : Fintype.card {e' : E // e' ≠ e} = m - 1 := by
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hE]
      have hm : 0 < m := by
        rw [← hE]
        exact Fintype.card_pos_iff.2 ⟨e⟩
      have i1 := IH (m - 1) (by omega) _ _ (cmap src e (src e) (tgt e) hloop)
        (cmap tgt e (src e) (tgt e) hloop) hcardE
      have hdeg1 : deg (dmap src e) (dmap tgt e) (src e) = 1 := by
        have h := deg_delete src tgt e (src e)
        have hne : tgt e ≠ src e := fun h => hloop h.symm
        simp only [hne, ite_true, ite_false] at h
        omega
      have i2 := pendant_step (m - 1) (fun m' hm' => IH m' (by omega)) (dmap src e)
        (dmap tgt e) hcardE (src e) hdeg1
      have hm2 : 2 ≤ m := by
        by_contra hlt
        have h0 : Fintype.card {e' : E // e' ≠ e} = 0 := by omega
        have : IsEmpty {e' : E // e' ≠ e} := Fintype.card_eq_zero_iff.1 h0
        unfold deg at hdeg1
        simp at hdeg1
      have e1 : cK ^ (m - 1) = cK ^ (m - 2) * cK := by
        rw [← pow_succ]
        congr 1
        omega
      have e2 : cK ^ (m - 1 - 1) = cK ^ (m - 2) := by
        congr 1
      have e3 : cK ^ m = cK ^ (m - 2) * cK ^ 2 := by
        rw [← pow_add]
        congr 1
        omega
      have hk : 0 < cK ^ (m - 2) := pow_pos cK_pos _
      have h4 : (numTrees src tgt : ℝ)
          ≤ numTrees (cmap src e (src e) (tgt e) hloop) (cmap tgt e (src e) (tgt e) hloop)
            + numTrees (dmap src e) (dmap tgt e) := by
        exact_mod_cast (by omega : numTrees src tgt
          ≤ numTrees (cmap src e (src e) (tgt e) hloop) (cmap tgt e (src e) (tgt e) hloop)
            + numTrees (dmap src e) (dmap tgt e))
      rw [e2] at i2
      rw [e1] at i1
      rw [e3]
      nlinarith [cK_add_one_le, mul_le_mul_of_nonneg_left cK_add_one_le hk.le]

/-- The bound in squared form, with non-strict inequality. -/
theorem numTrees_sq_le (V E : Type) [Fintype V] [Fintype E] (src tgt : E → V) :
    (numTrees src tgt : ℝ) ^ 2 ≤ (27 / 8 : ℝ) ^ Fintype.card E := by
  classical
  have h := numTrees_le_pow _ V E src tgt rfl
  calc (numTrees src tgt : ℝ) ^ 2 ≤ (cK ^ Fintype.card E) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h 2
    _ = (cK ^ 2) ^ Fintype.card E := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ = (27 / 8 : ℝ) ^ Fintype.card E := by rw [cK_sq]

/-- **The universal bound.** Every finite multigraph with `m ≥ 1` edges has fewer than
`(27/8)^(m/2)` spanning trees; in integers, `τ² · 8^m < 27^m`. -/
theorem kenyon_bound (V E : Type) [Fintype V] [Fintype E] (src tgt : E → V)
    (hm : 0 < Fintype.card E) :
    numTrees src tgt ^ 2 * 8 ^ Fintype.card E < 27 ^ Fintype.card E := by
  have h := numTrees_sq_le V E src tgt
  have h8 : (0:ℝ) < 8 ^ Fintype.card E := by positivity
  have hle : numTrees src tgt ^ 2 * 8 ^ Fintype.card E ≤ 27 ^ Fintype.card E := by
    have : (numTrees src tgt : ℝ) ^ 2 * 8 ^ Fintype.card E ≤ 27 ^ Fintype.card E := by
      rw [div_pow, le_div_iff₀ h8] at h
      exact h
    exact_mod_cast this
  refine lt_of_le_of_ne hle fun heq => ?_
  have hodd : Odd (27 ^ Fintype.card E) := Odd.pow (by decide)
  have heven : Even (numTrees src tgt ^ 2 * 8 ^ Fintype.card E) :=
    Even.mul_left (Nat.even_pow.2 ⟨by decide, hm.ne'⟩) _
  rw [heq] at heven
  exact (Nat.not_even_iff_odd.2 hodd) heven

/-- **The universal bound**, in the form of the paper. -/
theorem kenyon_bound_real (V E : Type) [Fintype V] [Fintype E] (src tgt : E → V)
    (hm : 0 < Fintype.card E) :
    (numTrees src tgt : ℝ) < (27 / 8 : ℝ) ^ ((Fintype.card E : ℝ) / 2) := by
  have h := kenyon_bound V E src tgt hm
  have h' : (numTrees src tgt : ℝ) ^ 2 < (27 / 8 : ℝ) ^ Fintype.card E := by
    have h1 : ((numTrees src tgt ^ 2 * 8 ^ Fintype.card E : ℕ) : ℝ)
        < ((27 ^ Fintype.card E : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h1
    rw [div_pow, lt_div_iff₀ (by positivity)]
    exact h1
  have hx : (27 / 8 : ℝ) ^ ((Fintype.card E : ℝ) / 2)
      = Real.sqrt ((27 / 8 : ℝ) ^ Fintype.card E) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [hx]
  exact Real.lt_sqrt_of_sq_lt h'

end Kenyon
