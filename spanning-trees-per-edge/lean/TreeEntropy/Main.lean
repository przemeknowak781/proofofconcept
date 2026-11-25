/-
  The edge inequality for the tree entropy: final statements.

  Data: a finite multigraph given by `src tgt : E → V` (loops and parallel edges allowed in the
  encoding), reals `x : V → ℝ` and `r : E → ℝ` with `r e > 0`.

  Hypotheses of `tree_entropy_bound`:
    (I1)  r e (1 + r e) = x (src e) · x (tgt e)                  for every edge;
    (I2)  the sum of `r` over the edge-ends at `v` is `deg v · x v - 1`   for every vertex;
    (D)   every degree is at least 2 and no edge joins two vertices of degree 2;
    (R)   with `rbar v = x v - 1/deg v`:
            deg v = 2                                   ⟹ rbar v ≤ 1,
            deg v = d ≥ 3                               ⟹ rbar v ≤ 3/d,
            deg v = d ≥ 3, some neighbour of degree ≥ 3 ⟹ rbar v ≤ (9d - 1)/(d (3d + 1)).

  Conclusion:
      ∑ e, log (1 + r e) - ∑ v, log (x v) ≤ |E| · (1/2) · log (27/8).

  `tree_entropy_bound_five` is the same conclusion from a weaker third range: it is required
  only of vertices of degree exactly 5 (value `11/20 = (9·5 - 1)/(5 (3·5 + 1))`).
  `edge_bound` is the per-edge inequality behind both.
-/
import TreeEntropy.Table
import TreeEntropy.Large

open Finset

namespace TreeEntropy

/-- The right end of the range of a vertex of degree `d ≥ 3` with a neighbour of degree `≥ 3`
(written `R^*_d` in the paper). -/
noncomputable def Rprime (d : ℕ) : ℝ := (9 * (d:ℝ) - 1) / (d * (3 * d + 1))

theorem Rprime_five : Rprime 5 = 11 / 20 := by
  unfold Rprime; norm_num

/-- **The per-edge inequality.**  `a, b` are the degrees of the two ends.  The refined range
`11/20` is asked only of an end of degree 5 whose other end has degree at least 3. -/
theorem edge_bound {a b : ℕ} {xu xv r : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : ¬(a = 2 ∧ b = 2))
    (hr : 0 < r) (hρu : 0 < xu - 1 / (a:ℝ)) (hρv : 0 < xv - 1 / (b:ℝ))
    (I1 : r * (1 + r) = xu * xv)
    (hu2 : a = 2 → xu - 1 / (a:ℝ) ≤ 1) (hu3 : 3 ≤ a → xu - 1 / (a:ℝ) ≤ 3 / (a:ℝ))
    (hv2 : b = 2 → xv - 1 / (b:ℝ) ≤ 1) (hv3 : 3 ≤ b → xv - 1 / (b:ℝ) ≤ 3 / (b:ℝ))
    (hu5 : a = 5 → 3 ≤ b → xu - 1 / (a:ℝ) ≤ 11 / 20)
    (hv5 : b = 5 → 3 ≤ a → xv - 1 / (b:ℝ) ≤ 11 / 20) :
    Real.log (1 + r) - 1 / (a:ℝ) * Real.log xu - 1 / (b:ℝ) * Real.log xv
      - gp (xu - 1 / (a:ℝ)) * (r - (xu - 1 / (a:ℝ)))
      - gp (xv - 1 / (b:ℝ)) * (r - (xv - 1 / (b:ℝ)))
      ≤ 1 / 2 * Real.log (27 / 8) := by
  have ha0 : (0:ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hb0 : (0:ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hinva : 0 < 1 / (a:ℝ) := by positivity
  have hinvb : 0 < 1 / (b:ℝ) := by positivity
  have hxu : 0 < xu := by linarith
  have hxv : 0 < xv := by linarith
  -- an end of degree at least 120
  rcases Nat.lt_or_ge b 120 with hb120 | hb120
  swap
  · exact caseC_bound ha hb120 hr hρu hρv I1 hu2 hu3 (hv3 (by omega))
  rcases Nat.lt_or_ge a 120 with ha120 | ha120
  swap
  · have h := caseC_bound (a := b) (b := a) (xu := xv) (xv := xu) hb ha120 hr hρv hρu
      (by rw [I1]; ring) hv2 hv3 (hu3 (by omega))
    linarith
  -- both degrees below 120
  have hE := edge_le_f (a := (a:ℝ)) (b := (b:ℝ)) hr hρu hρv hxu hxv I1
  have e5 : (9 * ((5:ℕ):ℝ) - 1) / (((5:ℕ):ℝ) * (3 * ((5:ℕ):ℝ) + 1)) = 11 / 20 := by norm_num
  rcases Nat.eq_or_lt_of_le ha with ha2 | ha3
  · have hb3 : 3 ≤ b := by omega
    have e : (a:ℝ) = 2 := by exact_mod_cast ha2.symm
    have h1 : f (a:ℝ) (xu - 1 / (a:ℝ))
        ≤ 1 / 4 * Real.log (27 / 8) - 1 / 16 * Real.log 2 := by
      rw [e] at hρu ⊢
      exact two_bound hρu
    have h2 := caseB_bound hb3 hb120 hρv (hv3 hb3)
    linarith
  · rcases Nat.eq_or_lt_of_le hb with hb2 | hb3
    · have e : (b:ℝ) = 2 := by exact_mod_cast hb2.symm
      have h1 : f (b:ℝ) (xv - 1 / (b:ℝ))
          ≤ 1 / 4 * Real.log (27 / 8) - 1 / 16 * Real.log 2 := by
        rw [e] at hρv ⊢
        exact two_bound hρv
      have h2 := caseB_bound ha3 ha120 hρu (hu3 ha3)
      linarith
    · have k1 : f (a:ℝ) (xu - 1 / (a:ℝ)) ≤ 1 / 4 * Real.log (27 / 8) := by
        rcases eq_or_ne a 5 with h5 | h5
        · have h := hu5 h5 hb3
          subst h5
          exact caseA_bound ha3 ha120 hρu (by rw [e5]; exact h)
        · exact caseA3_bound ha3 ha120 h5 hρu (hu3 ha3)
      have k2 : f (b:ℝ) (xv - 1 / (b:ℝ)) ≤ 1 / 4 * Real.log (27 / 8) := by
        rcases eq_or_ne b 5 with h5 | h5
        · have h := hv5 h5 ha3
          subst h5
          exact caseA_bound hb3 hb120 hρv (by rw [e5]; exact h)
        · exact caseA3_bound hb3 hb120 h5 hρv (hv3 hb3)
      linarith

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

omit [Fintype V] in
theorem endSum_pos (src tgt : E → V) (r : E → ℝ) (hr : ∀ e, 0 < r e) {v : V}
    (hdeg : 0 < deg src tgt v) : 0 < endSum src tgt r v := by
  unfold endSum
  unfold deg at hdeg
  have h1 : 0 ≤ ∑ e ∈ univ.filter (fun e => src e = v), r e :=
    Finset.sum_nonneg fun e _ => (hr e).le
  have h2 : 0 ≤ ∑ e ∈ univ.filter (fun e => tgt e = v), r e :=
    Finset.sum_nonneg fun e _ => (hr e).le
  have hc : 0 < (univ.filter fun e => src e = v).card
      ∨ 0 < (univ.filter fun e => tgt e = v).card := by
    omega
  rcases hc with hc | hc
  · have := Finset.sum_pos (fun e _ => hr e) (Finset.card_pos.1 hc)
    linarith
  · have := Finset.sum_pos (fun e _ => hr e) (Finset.card_pos.1 hc)
    linarith

omit [Fintype V] in
/-- `rbar v = x v - 1/deg v` is positive: it equals `(sum of r over the ends at v)/deg v`. -/
theorem rbar_pos (src tgt : E → V) (x : V → ℝ) (r : E → ℝ) (hr : ∀ e, 0 < r e)
    (I2 : ∀ v, endSum src tgt r v = deg src tgt v * x v - 1) {v : V}
    (hdeg : 0 < deg src tgt v) : 0 < x v - 1 / (deg src tgt v : ℝ) := by
  have hd : (0:ℝ) < deg src tgt v := by exact_mod_cast hdeg
  have h := endSum_pos src tgt r hr hdeg
  rw [I2 v] at h
  have e : x v - 1 / (deg src tgt v : ℝ)
      = ((deg src tgt v : ℝ) * x v - 1) / (deg src tgt v : ℝ) := by
    field_simp
  rw [e]
  exact div_pos h hd

/-- **The edge inequality of the paper (Lemma 'edge inequality': Phi(G) <= m L) from a weaker
third range.**  Here Phi(G) is written as `∑ e, log (1 + r e) - ∑ v, log (x v)`; that this
equals the tree entropy is the closed formula of the paper, which is not formalised.  The
refined bound `rbar v ≤ 11/20` is
required only of a vertex of degree exactly 5 that some edge joins to a vertex of degree
at least 3. -/
theorem tree_entropy_bound_five (src tgt : E → V) (x : V → ℝ) (r : E → ℝ)
    (hr : ∀ e, 0 < r e)
    (I1 : ∀ e, r e * (1 + r e) = x (src e) * x (tgt e))
    (I2 : ∀ v, endSum src tgt r v = deg src tgt v * x v - 1)
    (hdeg : ∀ v, 2 ≤ deg src tgt v)
    (hD : ∀ e, ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2))
    (R2 : ∀ v, deg src tgt v = 2 → x v - 1 / (deg src tgt v : ℝ) ≤ 1)
    (R3 : ∀ v, 3 ≤ deg src tgt v → x v - 1 / (deg src tgt v : ℝ) ≤ 3 / (deg src tgt v : ℝ))
    (R5 : ∀ v, deg src tgt v = 5 →
      (∃ e, (src e = v ∧ 3 ≤ deg src tgt (tgt e)) ∨ (tgt e = v ∧ 3 ≤ deg src tgt (src e))) →
      x v - 1 / (deg src tgt v : ℝ) ≤ 11 / 20) :
    ∑ e, Real.log (1 + r e) - ∑ v, Real.log (x v)
      ≤ (Fintype.card E : ℝ) * (1 / 2 * Real.log (27 / 8)) := by
  have hpos : ∀ v, 0 < deg src tgt v := fun v => by have := hdeg v; omega
  refine sum_le_of_edge src tgt x (fun v => gp (x v - 1 / (deg src tgt v : ℝ))) r _ hpos I2 ?_
  intro e
  exact edge_bound (hdeg (src e)) (hdeg (tgt e)) (hD e) (hr e)
    (rbar_pos src tgt x r hr I2 (hpos (src e))) (rbar_pos src tgt x r hr I2 (hpos (tgt e)))
    (I1 e) (R2 (src e)) (R3 (src e)) (R2 (tgt e)) (R3 (tgt e))
    (fun h5 ht => R5 (src e) h5 ⟨e, Or.inl ⟨rfl, ht⟩⟩)
    (fun h5 hs => R5 (tgt e) h5 ⟨e, Or.inr ⟨rfl, hs⟩⟩)

/-- **The edge inequality of the paper (Lemma 'edge inequality': Phi(G) <= m L).**  Here Phi(G)
is written as `∑ e, log (1 + r e) - ∑ v, log (x v)`; that this equals the tree entropy is the
closed formula of the paper, which is not formalised.  The third range is required of a vertex of degree `d ≥ 3` as soon as
some edge joins it to a vertex of degree `≥ 3`. -/
theorem tree_entropy_bound (src tgt : E → V) (x : V → ℝ) (r : E → ℝ)
    (hr : ∀ e, 0 < r e)
    (I1 : ∀ e, r e * (1 + r e) = x (src e) * x (tgt e))
    (I2 : ∀ v, endSum src tgt r v = deg src tgt v * x v - 1)
    (hdeg : ∀ v, 2 ≤ deg src tgt v)
    (hD : ∀ e, ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2))
    (R2 : ∀ v, deg src tgt v = 2 → x v - 1 / (deg src tgt v : ℝ) ≤ 1)
    (R3 : ∀ v, 3 ≤ deg src tgt v → x v - 1 / (deg src tgt v : ℝ) ≤ 3 / (deg src tgt v : ℝ))
    (R3' : ∀ v, 3 ≤ deg src tgt v →
      (∃ e, (src e = v ∧ 3 ≤ deg src tgt (tgt e)) ∨ (tgt e = v ∧ 3 ≤ deg src tgt (src e))) →
      x v - 1 / (deg src tgt v : ℝ) ≤ Rprime (deg src tgt v)) :
    ∑ e, Real.log (1 + r e) - ∑ v, Real.log (x v)
      ≤ (Fintype.card E : ℝ) * (1 / 2 * Real.log (27 / 8)) := by
  refine tree_entropy_bound_five src tgt x r hr I1 I2 hdeg hD R2 R3 ?_
  intro v h5 hex
  have h := R3' v (by omega) hex
  have e : Rprime (deg src tgt v) = 11 / 20 := by rw [h5]; exact Rprime_five
  rw [e] at h
  exact h

end TreeEntropy
