# Spanning trees per edge: a sharp bound and a question of Kenyon

*With a Lean 4 formalisation of the bound and of its sharpness (version 2), and computer certificates.*

Paper: [`paper/spanning_trees_per_edge.pdf`](paper/spanning_trees_per_edge.pdf) (LaTeX source in `paper/`),
by Filip Majchrzak (SAPIO MORPHEUS project).

Archived versions on Zenodo: version 2.0.0, DOI [10.5281/zenodo.24523144](https://doi.org/10.5281/zenodo.24523144);
version 1.0.0, DOI [10.5281/zenodo.24504455](https://doi.org/10.5281/zenodo.24504455); all versions, DOI
[10.5281/zenodo.24504454](https://doi.org/10.5281/zenodo.24504454). The paper of version 1 is kept in
[`paper/v1.0.0/`](paper/v1.0.0/); changes are listed in [`CHANGELOG.md`](CHANGELOG.md).

**New in version 2: both the universal bound and the sharpness of the constant are fully formalised in Lean 4**
(directory [`lean-kenyon/`](lean-kenyon/)).

## The statement

For every finite multigraph `G` with `m >= 1` edges, the number `tau(G)` of spanning trees satisfies

```
tau(G) < (27/8)^(m/2) = 1.8371...^m ,
```

and the base `sqrt(27/8)` cannot be lowered (connected 4-regular graphs of large girth, by theorems of McKay and
Lyons; version 2 also gives a direct proof on an explicit family of graphs, Section 10 of the paper).

In 1996 R. Kenyon asked: "Among all graphs with m edges, which graph G has the largest number of spanning trees
κ(G)? What is the sup of κ(G)^(1/m) over all graphs? Over planar graphs?" The statement above gives the supremum
over all graphs. The planar question (conjectured value 1.7916) and the question about the extremal graph for
each `m` are **not** answered. For planar graphs, and for determinants of link diagrams, the bound improves the
constant 1.8393 of Stoimenow slightly, to 1.8371.

## What has been checked, and what has not

- **Lean 4, the whole theorem and its sharpness (version 2, directory [`lean-kenyon/`](lean-kenyon/)).**
  Lean checks, with Mathlib: (1) `Kenyon.kenyon_bound`: for every finite multigraph given by two maps
  `src tgt : E → V` with `|E| >= 1`, `tau^2 * 8^|E| < 27^|E|`, with no hypothesis on the multigraph; (2)
  `Kenyon.kenyon_sharp`: for every real `0 < c < 27/8` there is a finite multigraph with `|E| >= 1` and
  `c^|E| < tau^2`. Here `tau` is defined as the number of sets `T` of edges with `|T| + 1 = |V|` that join every
  two vertices. These are Theorem 1 and Corollary 3 of the paper. No `sorry`; only the three standard axioms;
  every module is replayed in the kernel checker; a clean-room run with negative controls is recorded. The formal
  proof follows the second proof of the paper (Section 10; see
  [`lean-kenyon/PROOF_ROUTE.md`](lean-kenyon/PROOF_ROUTE.md)), not the proof of Sections 2 to 7.
  **Not formalised:** Proposition 2 in its generality (every sequence of connected 4-regular graphs of growing
  girth), Corollaries 4 and 5, the equality statement, and the lemmas of Sections 3 to 5 as stated there (hitting
  probabilities on the universal cover, the closed formula, the comparison of a graph with its cover); the formal
  proof does not use them. That the formal definition of `tau` is the number of spanning trees is a matter of
  reading four short definitions (quoted in [`lean-kenyon/README.md`](lean-kenyon/README.md)).
- **Lean 4, the key inequality (version 1, directory [`lean/`](lean/), unchanged).** The a priori bounds on the dart
  function, the two identities, the ranges and the edge inequality (Sections 3 and 6 of the paper, as statements
  about real numbers). Lean checks: if `h` is a positive function on the darts of a finite multigraph with
  minimum degree at least 2 and no edge between two vertices of degree 2, `h` satisfies the first-step equation and
  is the pointwise limit of a sequence that starts at 0 and satisfies the truncated first-step inequality, then
  `sum_v log(d_v - sum_{u~v} h_{u->v}) - sum_e log(1 - q_e) <= m * (1/2) * log(27/8)`. No `sorry`; only the three
  standard axioms; the finite table for degrees 2 to 119 consists of integer inequalities evaluated by the Lean
  kernel. In version 1 this was the only formalised part. Its modules are used, unchanged, by the package of
  version 2.
- **Interval arithmetic.** The numerical inequalities of the proof are certified independently with 60-digit
  interval arithmetic at explicit rational points (`verify/certify_intervals.py`).
- **Exhaustive check.** The theorem was confirmed in exact integer arithmetic for all 8,350,006 connected loopless
  multigraphs with at most 14 edges that are not trees (`verify/exhaustive.py`). This is a sanity check far from
  the sharp regime (the largest value found is 1.667 against 1.837).
- **Recomputation.** Separate AI agents of the same project re-derived each step of the proof and of the paper and
  recomputed the numerical claims with their own code.

**Not done:** no external expert has reviewed the paper or the formalisation. The literature search was limited to
open sources (see the paper, Section 8) and was not repeated for the second proof. We make no priority claim beyond
what the paper states, and we welcome corrections.

## Reproduce the computer checks

Requirements: Python 3 with `mpmath` and `numpy`; for the exhaustive check also `nauty` (`geng`, `multig`).

```bash
cd verify
python3 certify_intervals.py        # interval-arithmetic certificate of the numerical lemma; prints ALL CERTIFIED
python3 check_class.py 3 300        # consistency check on random multigraphs (not part of the proof)
python3 exhaustive.py 11            # tau^2 * 8^m < 27^m for all connected loopless multigraphs with m <= 11 (about a minute)
python3 exhaustive.py 14            # the same up to 14 edges, about 3 minutes on 4 cores (recorded: exhaustive_m14.out)
```

Recorded outputs: `verify/*.out`.

## The Lean packages

Both use Lean `leanprover/lean4:v4.37.0-rc1` and Mathlib commit `53dad9ed98be8416b6ca1111e55a03de4303231f`.

**`lean-kenyon/` (version 2): the bound and its sharpness.**

```bash
cd lean-kenyon
lake exe cache get      # prebuilt Mathlib
./scripts/check.sh      # prints "OK: build, 39 axiom reports, kernel replay of 29 modules"
```

The main statements are `Kenyon.kenyon_bound`, `Kenyon.kenyon_bound_real` (`lean-kenyon/Kenyon/Main.lean`) and
`Kenyon.kenyon_sharp` (`lean-kenyon/Kenyon/Sharp.lean`). See [`lean-kenyon/README.md`](lean-kenyon/README.md) for
the exact statements and the definitions to read, [`lean-kenyon/PROOF_ROUTE.md`](lean-kenyon/PROOF_ROUTE.md) for
the steps of the proof, and [`lean-kenyon/VERIFICATION_CLEANROOM.txt`](lean-kenyon/VERIFICATION_CLEANROOM.txt)
with [`lean-kenyon/logs/`](lean-kenyon/logs/) for a recorded run.

**`lean/` (version 1, unchanged): the edge inequality.**

```bash
cd lean
lake exe cache get      # prebuilt Mathlib
./scripts/check.sh      # build, placeholder scan, axiom report, controls, kernel replay
```

The main statements are `TreeEntropy.tree_entropy_bound` (`lean/TreeEntropy/Main.lean`) and
`TreeEntropy.tree_entropy_bound_of_first_step` (`lean/TreeEntropy/APriori.lean`). See
[`lean/README.md`](lean/README.md) for the exact statements and
[`lean/VERIFICATION_CLEANROOM.txt`](lean/VERIFICATION_CLEANROOM.txt) for a recorded run.

## Files

| Path | Content |
|---|---|
| `paper/` | the paper, version 2 (PDF and LaTeX); `paper/v1.0.0/` is the paper of version 1 |
| `verify/certify_intervals.py` | interval certificate for the one-variable inequalities and the constants of the proof |
| `verify/cover.py` | universal-cover quantities of a finite multigraph (hitting probabilities, closed formula, integral definition) |
| `verify/check_class.py` | random consistency check of the identities, ranges, closed formula and edge inequality |
| `verify/exhaustive.py` | exact exhaustive check of the theorem for small multigraphs |
| `lean-kenyon/` | Lean 4 package `Kenyon` (version 2): complete formal proofs of the bound and of its sharpness |
| `lean/` | Lean 4 package `TreeEntropy` (version 1, unchanged): Sections 3 and 6 of the paper as statements about real numbers |
| `CHANGELOG.md` | what changed between the versions |

## AI assistance

This work was carried out with substantial assistance from AI systems working under the author's direction.
The statement, the proof, the computations, the literature comparison and the manuscript were produced by AI
agents based on Anthropic's Claude; separate AI agents of the same project refereed the proof and the text,
wrote the Lean formalisation of the key inequality and searched the literature. The second proof (Section 10 of the
paper) and its complete Lean formalisation (version 2) were produced by an AI agent based on Anthropic's Claude;
every step is checked by Lean. The definitions and the final statements were also read in the Lean source by the
author's AI assistants, including a system from a second developer. This is not an external expert review.
The author selected the direction, directed the work, made the publication decisions and is responsible for the
content.

## License

Code: Apache License 2.0. Paper: CC BY 4.0.
