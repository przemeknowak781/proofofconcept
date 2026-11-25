# Changes

## Version 2.0.0 (25 November 2026)

Zenodo: [10.5281/zenodo.24523144](https://doi.org/10.5281/zenodo.24523144).

* **New: complete Lean 4 formalisation of the bound and of its sharpness** (directory
  `lean-kenyon/`). `Kenyon.kenyon_bound`: every finite multigraph with `m ≥ 1` edges satisfies
  `τ² · 8^m < 27^m`. `Kenyon.kenyon_sharp`: for every `0 < c < 27/8` there is a multigraph with
  `c^m < τ²`. These are Theorem 1 and Corollary 3 of the paper. Recorded clean-room run and raw
  outputs: `lean-kenyon/VERIFICATION_CLEANROOM.txt`, `lean-kenyon/logs/`.
* **New: Section 10 of the paper**, a second proof of Theorem 1 and a direct proof of the lower
  bound in Corollary 3. This is the route that Lean checks; it is also listed, with the names of
  the Lean theorems, in `lean-kenyon/PROOF_ROUTE.md`.
* The paper's title line, abstract, the paragraph on the status of verification, Appendix A and
  the statement on the use of AI are updated accordingly. Sections 2 to 9 of the paper are
  unchanged.
* Unchanged: the statements of the paper, the first proof (Sections 2 to 7), the literature
  section with its limits, `verify/`, and the Lean package of version 1 in `lean/`.
* Not formalised: Proposition 2 in its generality, Corollaries 4 and 5, the equality statement,
  and the lemmas of Sections 3 to 5 as stated there. See the paper and `lean-kenyon/README.md`.

## Version 1.0.0 (24 November 2026)

Zenodo: [10.5281/zenodo.24504455](https://doi.org/10.5281/zenodo.24504455).

The paper, the verification scripts and the Lean package `TreeEntropy` for the key inequality
(`lean/`). In this version the theorem as a whole was not machine-checked. The paper of version 1
is kept in `paper/v1.0.0/`.
