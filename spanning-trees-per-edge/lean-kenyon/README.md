# Kenyon — the bound `τ < (27/8)^(m/2)` and its sharpness in Lean 4

Lean 4 / Mathlib formalisation of Theorem 1 and Corollary 3 of the paper
*Spanning trees per edge: a sharp bound and a question of Kenyon* (version 2): the bound
`τ(G) < (27/8)^(m/2)` for every finite multigraph with `m ≥ 1` edges, and
`sup_G τ(G)^(1/m) = √(27/8)`, not attained.

```lean
/-- Every finite multigraph with m ≥ 1 edges has fewer than (27/8)^(m/2) spanning trees. -/
theorem Kenyon.kenyon_bound (V E : Type) [Fintype V] [Fintype E] (src tgt : E → V)
    (hm : 0 < Fintype.card E) :
    numTrees src tgt ^ 2 * 8 ^ Fintype.card E < 27 ^ Fintype.card E

theorem Kenyon.kenyon_bound_real (V E : Type) [Fintype V] [Fintype E] (src tgt : E → V)
    (hm : 0 < Fintype.card E) :
    (numTrees src tgt : ℝ) < (27 / 8 : ℝ) ^ ((Fintype.card E : ℝ) / 2)

/-- The constant 27/8 cannot be lowered. -/
theorem Kenyon.kenyon_sharp (c : ℝ) (hc0 : 0 < c) (hc : c < 27 / 8) :
    ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (src tgt : E → V),
      0 < Fintype.card E ∧ c ^ Fintype.card E < (numTrees src tgt : ℝ) ^ 2
```

There is no hypothesis on the multigraph in `kenyon_bound`: loops, multiple edges and
disconnected graphs are allowed. Every theorem depends only on the axioms `propext`,
`Classical.choice`, `Quot.sound`.

Proposition 2 of the paper (the limit for every sequence of connected 4-regular graphs of growing
girth, quoted there from McKay and Lyons) is **not** formalised; the lower bound for the supremum
is proved here directly, on an explicit family of graphs.

| Pin | Value |
| --- | --- |
| Lean | `4.37.0-rc1`, see `lean-toolchain` |
| Mathlib | commit `53dad9ed98be8416b6ca1111e55a03de4303231f`, see `lakefile.toml`, `lake-manifest.json` |

The directory [`../lean/`](../lean/) is the package of version 1 (the edge inequality only). It
is kept unchanged. Its eight modules `TreeEntropy/*` are copied here without change and are used
by the proof.

## How to check

Requirements: [elan](https://github.com/leanprover/elan), git, about 8 GB of free disk space.

```bash
lake exe cache get        # pre-built Mathlib for the pinned commit
./scripts/check.sh        # prints "OK: build, 39 axiom reports, kernel replay of 29 modules"
```

`scripts/check.sh` runs, and fails if any step fails: `lake build`; a scan of the sources for
`sorry`, `admit`, `axiom`, `native_decide`; `scripts/PrintAxioms.lean` (for 39 theorems every
axiom used must be one of the three above); `leanchecker` (replay of every declaration in the
Lean kernel) on the 29 modules that contain declarations. During the build Lake prints a hint
about the module system for every Mathlib import; it is not an error.

A recorded run in a clean directory, with three negative controls, is in
[`VERIFICATION_CLEANROOM.txt`](VERIFICATION_CLEANROOM.txt); the raw outputs are in `logs/`.

## The definitions to read

A multigraph is a pair of maps `src tgt : E → V` on finite types (an edge `e` joins `src e` and
`tgt e`; a loop has `src e = tgt e`). The meaning of the theorems rests on four definitions in
`Kenyon/Forest.lean`:

```lean
def Adj (src tgt : E → V) (F : Finset E) (x y : V) : Prop :=
  ∃ e ∈ F, (src e = x ∧ tgt e = y) ∨ (src e = y ∧ tgt e = x)
def Conn (src tgt : E → V) (F : Finset E) : V → V → Prop :=
  Relation.ReflTransGen (Adj src tgt F)
def IsTree (src tgt : E → V) (T : Finset E) : Prop :=
  T.card + 1 = Fintype.card V ∧ ∀ x y, Conn src tgt T x y
noncomputable def numTrees (src tgt : E → V) : ℕ :=
  ((univ : Finset (Finset E)).filter fun T => IsTree src tgt T).card
```

A spanning tree is a set of `|V| − 1` edges that joins every two vertices. `Kenyon/Examples.lean`
checks the count on two small cases: one vertex with a loop has `1` spanning tree, two vertices
with two parallel edges have `2`.

## How the proof goes

The formal proof follows the second proof of the paper (Section 10), not the proof of its
Sections 2 to 7: there is no universal cover, no random walk, no power series and no analytic
continuation. The steps, with the names of the Lean theorems, are listed in
[`PROOF_ROUTE.md`](PROOF_ROUTE.md).

**Upper bound.**

| Module | Content |
| --- | --- |
| `TreeEntropy/*` | the edge inequality (package of version 1), unchanged |
| `Levels` | the dart system `h_{u→v} (d_u − z Σ h) = z` with a parameter `z ∈ [0,1]`; its least solution as a monotone limit; `xi_one_le`: the edge inequality applies to it at `z = 1` |
| `Green` | maximum principle; if `g ≥ 0` and `(D − zA) g ≥ 0` then `g(u) ≥ h_{u→v} g(v)` |
| `Super`, `BetheFun` | the Bethe functional increases along a segment of super-solutions |
| `OneStep` | `Xi z = Σ_v log P_v − Σ_e log (1 − q_e)`; `Xi b − Xi a ≥ −(b − a) Wsum b` |
| `LogDet` | `det N ≤ det M · exp (tr (M⁻¹N) − n)` for `M` positive definite, `N` positive semidefinite |
| `Lap` | `K(z) = D − zA`; `det K(b) ≤ det K(a) exp (−(b − a) Wsum a)` |
| `Bethe` | `det K(z) ≤ exp (Xi z)` for `0 ≤ z < 1`, by telescoping over a partition of `[0, z]` |
| `Forest`, `MatrixTree` | spanning trees and rooted forests; `det K(z) ≥ (1 − z) d_r z^(n−1) · numTrees` |
| `Count` | `numTrees ≤ n² e³ (27/8)^(m/2)` when every degree is ≥ 2 and no edge joins two vertices of degree 2 |
| `Amplify` | `N` copies glued at a vertex remove the factor `n² e³` |
| `Contract`, `Main` | deletion and contraction of an edge; induction on `m` for all multigraphs; strictness by parity |

**Sharpness.**

| Module | Content |
| --- | --- |
| `ForestCount`, `MatrixTree2` | counting lemma, extension of a rooted forest to a spanning tree, the other half of the matrix-tree theorem for rooted forests; `det K(z) ≤ numTrees · (1 + y)^(n+m)` for connected multigraphs with `(1 − z) d_v ≤ y²` |
| `Regular` | 4-regular multigraphs: the solution of the dart system is a constant `s(z) ≤ z/3`, `s(1) = 1/3`, `Xi 1 = n log (27/8)`, and `Xi b − Xi a ≤ −(b − a) Wsum a` |
| `Cayley` | graphs of an action of four letters; counters of walks without backtracking; if no reduced word of length `1..k+1` is closed, `K(t)⁻¹_{vv} ≤ (1 + t^(k+2)/(1 − t)) / P(t)` |
| `Sanov` | the group of permutations of `(ℤ/n)²` generated by `(x,y) ↦ (x+2y, y)` and `(x,y) ↦ (x, y+2x)`; for `3^J + 1 < n` no nonempty reduced word of length `≤ J` is trivial; the graph is connected |
| `Sharp` | `log det K(z) ≥ Xi z − n · 2 z^(k+1)/(1 − z)`; lower bound for `numTrees`; `kenyon_sharp` |

## What is NOT proved here

* The lemmas of Sections 3 to 5 of the paper as they are stated there (hitting probabilities on
  the universal cover, the spectral form of the matrix-tree theorem, the closed formula as a
  limit, the comparison of a graph with its cover) are not formalised and are not used. The two
  theorems are proved by the route of Section 10, which was found while formalising the theorem;
  it has been checked by Lean and by the AI agents that wrote it, not by an external expert.
* Proposition 2 of the paper in its generality (every sequence of connected 4-regular graphs of
  growing girth, with convergence of `numTrees^(1/m)`) is not formalised. The sharpness is proved
  for the family of `Kenyon/Sanov.lean`, and more generally (`Act.numTrees_ge`) for connected
  graphs of an action of four letters without short closed reduced words.
* Corollaries 4 and 5 of the paper (planar graphs and link determinants; the growth constant of
  the smallest current) and the equality statement of its Remark on equality are not formalised.
* The full matrix-tree theorem is present only in the form needed: both inequalities between
  `det (redMat Es R 0 z)` and `z^(|V|−|R|) · numForests Es R` (`numForests_le_det`,
  `det_le_numForests`). The equality is not stated as one theorem.
* Lean certifies the theorems for the definitions in these files. That `numTrees` is the number
  of spanning trees in the sense of the paper is a matter of reading the four definitions above.

## What is trusted

The Lean 4 kernel; the three standard axioms; Mathlib as distributed for the pinned commit (its
compiled files are downloaded and not replayed here); Lake and `leanchecker`.

## Authorship and licence

The proofs in this directory were written by an AI agent based on Anthropic's Claude, working
under the direction of Filip Majchrzak (SAPIO MORPHEUS project), who takes responsibility for the
content. No external expert has reviewed the formalisation. Licence of the code: Apache-2.0.
