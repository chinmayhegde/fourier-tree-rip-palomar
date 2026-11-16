# Fourier tree-RIP: Lean 4 formalization

**A Quadratic Lower Bound for Fourier RIP with Tree-Structured Sparsity**

This repository contains a formal Lean proof of a lower bound on the number of
uniformly sampled Fourier rows required for restricted isometry on vectors whose
supports are rooted connected subtrees of the canonical binary heap.

The principal theorem (`FourierTreeRIP.fourier_tree_rip_lower_bound`) asserts that
for any positive number of measurements `m`, whenever

```text
20000 * m <= k * min(k, log_2(N/k)),
```

at most half of the `N^m` ordered sequences of sampled frequencies satisfy
order-`k` tree-RIP with distortion `1/4`. The count is taken with replacement.
The quadratic-regime Lean corollary assumes `N >= k * 2^k`. The more general
bound is given directly by the principal theorem. These exact statements should
be used in preference to the asymptotic formulation in the accompanying note.

## Contents

- [`Challenge.lean`](Challenge.lean) — concise, self-contained, mathematically
  auditable definitions and five comparison statements. Only allowlisted
  Mathlib imports; intentional `sorry` placeholders.
- [`Solution.lean`](Solution.lean) — proofs of the exact same five declarations.
- [`TreeRIP/`](TreeRIP/) — substantive proof library: Fejér estimates,
  simultaneous approximation, broom construction, finite counting, optimization,
  and full-DFT Parseval.
- [`comparator.json`](comparator.json) — Comparator declaration list and axiom policy.
- [`formalization.yaml`](formalization.yaml) — provenance, authorship, AI disclosure,
  review, source correspondence, and theorem limitations.
- [`paper/tree_fourier_rip_note.pdf`](paper/tree_fourier_rip_note.pdf) — mathematical
  source note (five pages).
- [`.github/workflows/ci.yml`](.github/workflows/ci.yml) — source policy,
  metadata validation, Lean build, and independent Comparator CI.

## Verification

Prerequisites: Lean 4.35.0 (pinned in `lean-toolchain`), Linux, Git, Python 3,
Ruby, and `bubblewrap` (`bwrap`). A substantial Mathlib build/cache download
is required. Dependencies are pinned by `lake-manifest.json`.

```bash
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
lake exe cache get
lake build
./scripts/verify-comparator.sh
```

The `Challenge.lean` `sorry`s are **deliberate** and are never imported by the
proved `Solution.lean`. The substantive development has no `sorry`, `admit`,
custom `axiom`, or `native_decide`. Comparator must accept the five statements
and confirm the permitted axiom closure. **The module-system conversion and
this exact repository commit must be rebuilt and rechecked**: a previous
Comparator pass on the pre-port source does not establish a pass on new bytes.

## Provenance and scope

The mathematical source is the included five-page note. A Claude agent
formalized the argument; the project owner reported an earlier Comparator pass.
An OpenAI GPT-6 inspection was source-level only. The repository documents
all known statement differences in `formalization.yaml`, including the stronger
ambient-size hypothesis in the explicitly named quadratic corollary.
The note's discussion of bit-reversal, sampling without replacement, and
Fourier/wavelet models is not claimed as proved here.

## Palomar submission

The repository can be private during development. **Palomar requires a PUBLIC
GitHub repository at the exact submitted 40-character commit SHA.** After all
CI jobs pass, change the repo to public if necessary and obtain the revision:

```bash
git rev-parse HEAD
```

Submit the public repository URL and the full SHA at
https://submit.palomar-registry.org/ . Palomar mechanically checks the exact
commit and conducts a separate review; passing the local checks is not approval.

## License

Code: Apache-2.0 (see `LICENSE`). The cited mathematical source is included for
review and is not asserted to be relicensed by the code license.
