# A Quadratic Lower Bound for Fourier RIP with Tree-Structured Sparsity

This repository contains a Lean 4 formalization of a lower bound for partial Fourier measurements of vectors supported on rooted connected subtrees of the canonical binary heap.

## Result

Consider an \(N \times N\) discrete Fourier transform, with \(m\) rows sampled independently and uniformly **with replacement**, normalized by \(1/\sqrt{m}\). The main theorem shows that, for \(m > 0\), if

\[
20000\,m \leq k\min\!\left\{k,\log_2(N/k)\right\},
\]

then **at least half** of all ordered frequency samples fail tree-restricted isometry of order \(k\) with distortion \(1/4\).

In particular, when \(N \geq k2^k\) and \(20000\,m \leq k^2\), tree-RIP fails with probability at least \(1/2\). Thus, in this ambient-dimension regime, uniformly subsampled Fourier measurements face a quadratic \(\Omega(k^2)\) obstruction, in contrast to the linear measurement complexity possible with Gaussian matrices for tree-sparse signals.

The proof constructs *broom* (stem-plus-bush) tree supports and combines Fejér-kernel estimates, simultaneous Diophantine approximation, and finite counting. It also formalizes full-DFT Parseval as a consistency check.

## Contents

- [`Challenge.lean`](Challenge.lean) — definitions and the five theorem statements.
- [`Solution.lean`](Solution.lean) — proofs of the five statements, using the supporting library.
- [`TreeRIP/`](TreeRIP/) — tree and broom constructions, kernel estimates, Diophantine approximation, counting, parameter optimization, and Parseval.
- [`paper/tree_fourier_rip_note.pdf`](paper/tree_fourier_rip_note.pdf) — accompanying mathematical note.
- [`formalization.yaml`](formalization.yaml) — formalization metadata and correspondence with the note.
- [`comparator.json`](comparator.json) — declarations checked by Comparator.
- [`lakefile.toml`](lakefile.toml), [`lean-toolchain`](lean-toolchain), and [`lake-manifest.json`](lake-manifest.json) — pinned Lean and Mathlib configuration.
- [`scripts/`](scripts/) and [`.github/workflows/ci.yml`](.github/workflows/ci.yml) — source checks and automated build/Comparator checks.
