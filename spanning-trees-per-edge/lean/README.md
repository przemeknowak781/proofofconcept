# TreeEntropy — the edge inequality in Lean 4

Lean 4 / Mathlib formalisation of one part of the proof in the paper
*Spanning trees per edge: a sharp bound and a question of Kenyon*.

The paper proves that every finite multigraph with `m ≥ 1` edges has fewer than `(27/8)^(m/2)`
spanning trees. **This package does not formalise that theorem.** It formalises the analytic core
of the proof as statements about real numbers:

* the edge inequality (in the paper: Lemma "edge inequality", `Phi(G) <= m L`, `L = (1/2) log(27/8)`);
* the algebra of the section on the universal cover that feeds it: the a priori bounds, the two
  identities, and the three ranges.

What is and is not covered is listed precisely below.

## The statements

Encoding. `V` and `E` are finite types; an edge `e` has ends `src e` and `tgt e` (parallel edges
and loops are allowed by the encoding). `deg src tgt v` is the number of edge-ends at `v`, and
`endSum src tgt r v` is the sum of `r` over the edge-ends at `v`.
`Rprime d = (9d − 1)/(d(3d + 1))` is the number written `R^*_d` in the paper.

### 1. The edge inequality (`TreeEntropy/Main.lean`)

```lean
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
      ≤ (Fintype.card E : ℝ) * (1 / 2 * Real.log (27 / 8))
```

Hypotheses in plain words:

1. `r_e > 0` on every edge. Positivity of `x_v` is not assumed; it follows from the second identity.
2. First identity: `r_e (1 + r_e) = x_u x_v` for every edge `e = uv`.
3. Second identity: the sum of `r` over the edge-ends at `v` equals `d_v x_v − 1`.
4. Degree condition: every degree is at least 2 and no edge joins two vertices of degree 2.
5. Ranges for `x_v − 1/d_v`: at most `1` if `d_v = 2`; at most `3/d` if `d_v = d ≥ 3`; at most
   `(9d − 1)/(d(3d + 1))` if `d_v = d ≥ 3` and some edge joins `v` to a vertex of degree `≥ 3`.

Conclusion: `Σ_e log(1 + r_e) − Σ_v log x_v ≤ m · (1/2) · log(27/8)`.

`tree_entropy_bound_five` proves the same conclusion when the third range is required only of
vertices of degree exactly 5 (value `11/20`). `edge_bound` is the inequality for a single edge.

### 2. From a dart function (`TreeEntropy/Darts.lean`, `TreeEntropy/APriori.lean`)

Each edge `e` carries two reals: `hp e` for the dart `src e → tgt e` and `hm e` for the dart
`tgt e → src e`. `inSum v` is the sum of the values of the darts pointing into `v`. As in the
paper, `x_v = 1/(d_v − inSum v)`, `q_e = hp e · hm e`, `r_e = q_e/(1 − q_e)`.

```lean
theorem tree_entropy_bound_of_first_step [Fintype V] (src tgt : E → V) (hp hm : E → ℝ)
    (Hp Hm : ℕ → E → ℝ)
    (hdeg : ∀ v, 2 ≤ deg src tgt v)
    (hD : ∀ e, ¬(deg src tgt (src e) = 2 ∧ deg src tgt (tgt e) = 2))
    (pos_p : ∀ e, 0 < hp e) (pos_m : ∀ e, 0 < hm e)
    (eq_p : ∀ e, hp e
      * ((deg src tgt (src e) : ℝ) - inSum src tgt hp hm (src e) + hm e) = 1)
    (eq_m : ∀ e, hm e
      * ((deg src tgt (tgt e) : ℝ) - inSum src tgt hp hm (tgt e) + hp e) = 1)
    (base : Bounded src tgt (Hp 0) (Hm 0))
    (step_p : ∀ t e, Hp (t + 1) e
      * ((deg src tgt (src e) : ℝ) - (inSum src tgt (Hp t) (Hm t) (src e) - Hm t e)) ≤ 1)
    (step_m : ∀ t e, Hm (t + 1) e
      * ((deg src tgt (tgt e) : ℝ) - (inSum src tgt (Hp t) (Hm t) (tgt e) - Hp t e)) ≤ 1)
    (limp : ∀ e, Tendsto (fun t => Hp t e) atTop (𝓝 (hp e)))
    (limm : ∀ e, Tendsto (fun t => Hm t e) atTop (𝓝 (hm e))) :
    ∑ v, Real.log ((deg src tgt v : ℝ) - inSum src tgt hp hm v)
        - ∑ e, Real.log (1 - hp e * hm e)
      ≤ (Fintype.card E : ℝ) * (1 / 2 * Real.log (27 / 8))
```

Hypotheses in plain words: the degree condition; `h` is positive and satisfies the first-step
equation `h_{u→v} · (d_u − sum of the darts into u other than v→u) = 1`; `h` is the pointwise
limit of a sequence of levels `h^(t)` whose level 0 satisfies the a priori bounds (`Bounded`; the
zero function does, see `bounded_zero`) and whose consecutive levels satisfy the truncated
first-step inequality `h^(t+1)_{u→v} · (d_u − sum of the level-t darts into u other than v→u) ≤ 1`.

On the way Lean proves, for a dart function satisfying the first-step equation and the a priori
bounds (`structure Darts`): the two identities (`Darts.I1`, `Darts.I2`), the three ranges
(`Darts.R2`, `Darts.R3`, `Darts.R3'`), and the a priori bounds themselves by induction on the
level (`bounded_step`, `bounded_iterate`, `bounded_of_tendsto`).

### 3. Consistency and sharpness (`TreeEntropy/Sharp.lean`)

Two vertices joined by four parallel edges, `x = 3/8`, `r = 1/8` (every dart equal to `1/3`):
all hypotheses of `tree_entropy_bound` hold and the conclusion holds with equality
(`Sharp.hyps_and_equality`); the dart function satisfies `Darts` (`Sharp.darts`); and
`tree_entropy_bound_of_first_step` applies to the constant sequence (`Sharp.first_step_instance`).
So the hypotheses are jointly satisfiable and the constant `(1/2) log(27/8)` cannot be lowered in
these statements.

## What is NOT covered

* That hitting probabilities of the simple random walk on the universal cover (in full and
  truncated to `t` steps) are positive, satisfy the first-step equation and its truncated
  inequality, and that the truncated ones converge to the full ones. These are exactly the
  hypotheses of `tree_entropy_bound_of_first_step`.
* The closed formula identifying `Σ_e log(1 + r_e) − Σ_v log x_v` with the tree entropy `Phi(G)`
  of the cover.
* The comparison of a finite graph with its universal cover, and the matrix-tree theorem.
* The reductions by induction on the number of edges, and the final limiting argument.
* The sharpness statement for 4-regular graphs of large girth.

The main theorem of the paper is therefore **not** machine-checked. What is machine-checked is
the chain: first-step relations ⟹ a priori bounds ⟹ identities and ranges ⟹ edge inequality.

## How the Lean proof relates to the paper

The statements are those of the paper. Three steps are carried out differently.

* The finitely many numerical inequalities for degrees 2–119, which the paper certifies with
  interval arithmetic, are here exact inequalities between natural numbers
  (`TreeEntropy/Table.lean`), evaluated by the Lean kernel (`decide +kernel`; no `native_decide`).
  In the case of an edge with an end of degree 2, the constant is relaxed by `(1/16) log 2` on the
  other end and tightened by the same amount on the degree-2 end.
* The case of an edge with an end of degree at least 120 (`TreeEntropy/Large.lean`) uses
  `log(1 + y) ≥ 2y/(y + 2)` and a rational estimate, for every degree `≥ 2` of the other end;
  numerically it needs only `log 2 < 7/10`, `log 3 ≥ log 2 + 2/5` and monotonicity of `(log t)/t`.
* All three ranges are obtained from one bound on the sum of incoming darts:
  `x_v = 1/(d_v − inSum v)` and `inSum v ≤ (3/4) d_v − 1/12` when one incoming dart starts at a
  vertex of degree `≥ 3`, which gives `x_v ≤ 12/(3d + 1)` and the third range exactly.

| Module | Content |
| --- | --- |
| `Sum.lean` | the summation identity for the edge quantities |
| `OneVar.lean` | bound by the one-variable functions `f_d`; derivative and its sign; `f_4(1/8) = (1/4) log(27/8)`; reduction of a value `f_d(p/s)` to an inequality between natural numbers |
| `Table.lean` | the finite tables for degrees 2–119 and the resulting bounds on the ranges |
| `Large.lean` | an edge with an end of degree at least 120 |
| `Main.lean` | `edge_bound`, `tree_entropy_bound_five`, `tree_entropy_bound` |
| `Darts.lean` | identities and ranges from a dart function |
| `APriori.lean` | a priori bounds by levels; `tree_entropy_bound_of_first_step` |
| `Sharp.lean` | the equality case and consistency of the hypotheses |

## How to run

Requirements: [elan](https://github.com/leanprover/elan) (it installs the toolchain named in
`lean-toolchain`), git, about 8 GB of disk for Mathlib.

```bash
lake exe cache get        # downloads the pre-built Mathlib
./scripts/check.sh        # prints "OK: build, 44 axiom reports, controls, kernel replay of 8 modules"
```

`scripts/check.sh` runs, and fails if any step fails:

1. `lake build`;
2. a scan of the sources for `sorry`, `admit`, `axiom`, `native_decide`;
3. `scripts/PrintAxioms.lean`: for 44 theorems, every axiom used must be one of `propext`,
   `Classical.choice`, `Quot.sound`;
4. `scripts/Controls.lean`: the table entry at degree 4 is an equality of natural numbers, and
   lowering the constant by one unit makes it false;
5. `scripts/MustFail.lean`: a false table entry must be rejected by the kernel;
6. `leanchecker` (kernel replay) on the 8 modules.

A record of a clean-room run is in `VERIFICATION_CLEANROOM.txt`.

## Versions

* Lean `4.37.0-rc1` (commit `0b77e12952ad39077d80d8bd6b66d601f225c321`), see `lean-toolchain`
* Mathlib commit `53dad9ed98be8416b6ca1111e55a03de4303231f`, see `lakefile.toml` and `lake-manifest.json`
