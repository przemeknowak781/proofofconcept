# Spanning trees per edge — proof and reproducible computations

**Filip Majchrzak is the author of the proof.** This repository contains the complete v2.0.0 release of his paper, *Spanning trees per edge: a sharp bound and a question of Kenyon*, together with an independent verification of the result. When citing the proof, please credit Filip Majchrzak and cite the [original Zenodo release](https://doi.org/10.5281/zenodo.24523144).

For every finite multigraph with $m \ge 1$ edges, the number $\tau$ of spanning trees satisfies $\tau^2 \cdot 8^m < 27^m$. The bound is sharp: the supremum of $\tau^{1/m}$ over all such multigraphs is $\sqrt{27/8}$. The paper gives an analytic proof and a second proof formalized in Lean 4. [Original source revision](https://github.com/kosza123/flow-certificate-thresholds/tree/b4c5b60f61766ea11cb7e72cc493181ac06f6c68)

| Task | Start here | Supporting material |
|---|---|---|
| Read the full proof | [Paper (PDF)](spanning-trees-per-edge/paper/spanning_trees_per_edge.pdf) | [LaTeX source](spanning-trees-per-edge/paper/spanning_trees_per_edge.tex) |
| Follow the Lean formalization | [Proof outline and lemma dependencies](spanning-trees-per-edge/lean-kenyon/PROOF_ROUTE.md) | [Upper bound](spanning-trees-per-edge/lean-kenyon/Kenyon/Main.lean) · [Sharpness](spanning-trees-per-edge/lean-kenyon/Kenyon/Sharp.lean) |
| Verify the release files | [Verification script](verify.py) | [Zenodo archive](vendor/spanning-trees-per-edge-v2.0.0.zip) · [Upstream Git tree](github-tree-24523144.json) |
| Reproduce the experiments and enumeration | [Reproduction guide (in Polish)](dokumentacja/odtworzenie.md) | [Author’s scripts](spanning-trees-per-edge/verify/) · [Independent enumeration](audyt/reproduce.py) · [Spanning-tree counter in C](audyt/count_trees.c) |
| Compare your results | [Counts and maxima by number of edges](audyt/exact-results.txt) | [Recorded run](audyt/odtworzenie.txt) · [Interval certificate and random-graph results](audyt/python-replay.txt) |
| Check what the audit covered | [Mathematical report (in Polish)](dokumentacja/02-matematyka.md) · [Verification history (in Polish)](dokumentacja/przebieg.md) | [Build log and axiom reports](audyt/lean-replay.log) · [Kernel replay log](audyt/kernel-direct.log) |
| Cite or reuse the work | [Author’s README and citation information](spanning-trees-per-edge/README.md) | [Apache 2.0](LICENSE) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) |

After cloning, run `python -I -B verify.py` from the repository root. This first check requires only Python 3.12. It compares all 76 release files against the Zenodo archive and their upstream Git object IDs.

**Verification results.** Both experiments reproduced the author’s recorded output line for line. The independent enumeration counted 8,350,006 isomorphism classes of connected, loopless multigraphs with at most 14 edges, excluding trees. For graphs with exactly 14 edges, the maximum was 1,280 spanning trees. The local Lean check compiled 31 project files, inspected 39 axiom reports, and replayed 29 modules in the kernel. Scientific priority and the sharp constant for planar graphs remain separate questions.

**Provenance and licenses.** The `spanning-trees-per-edge/` directory contains the author’s unmodified release. Its code and scripts use the Apache License 2.0. The paper’s text and figures use CC BY 4.0. The nauty 2.9.3 archive includes its own `COPYRIGHT` and `LICENSE-2.0.txt` files. The `audyt/` directory records the independent verification. Its copy of `reproduce.py` uses a reference-table path adapted to this repository’s layout.
