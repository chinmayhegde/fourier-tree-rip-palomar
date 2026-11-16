module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# Fourier tree-RIP: definitions

Coordinates `1, 2, …, N - 1` are the nodes of the canonical binary heap: node `j` has
children `2 j` and `2 j + 1`, i.e. the parent of `j ≥ 2` is `j / 2`, and `1` is the root.
(Coordinate `0` is not a node of the tree.)
-/

namespace FourierTreeRIP

/-- A finite set of heap nodes is a rooted connected subtree if every element is a node
(`≥ 1`) and the set is closed under taking parents. -/
def IsRootedSubtree (S : Finset ℕ) : Prop :=
  ∀ j ∈ S, 1 ≤ j ∧ (2 ≤ j → j / 2 ∈ S)

/-- `x : Fin N → ℂ` is `k`-tree-sparse: its support is contained in a rooted connected
subtree with at most `k` nodes. -/
def TreeSparse (N k : ℕ) (x : Fin N → ℂ) : Prop :=
  ∃ S : Finset ℕ, IsRootedSubtree S ∧ S.card ≤ k ∧ ∀ j : Fin N, x j ≠ 0 → (j : ℕ) ∈ S

/-- `‖A x‖₂²`, where `A` is the `m × N` matrix with entries
`A ℓ j = m^(-1/2) * exp (2 π i ω_ℓ j / N)`: the `m` rows of the `N × N` DFT with
frequencies `ω_0, …, ω_{m-1}`, rescaled so that `E ‖A x‖² = ‖x‖²` for uniform frequencies. -/
noncomputable def measNormSq (N m : ℕ) (ω : Fin m → Fin N) (x : Fin N → ℂ) : ℝ :=
  1 / (m : ℝ) * ∑ ℓ : Fin m,
    ‖∑ j : Fin N, x j *
      Complex.exp (2 * Real.pi * Complex.I * ((ω ℓ : ℕ) : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ))‖ ^ 2

/-- Tree-RIP of order `k` with constant `δ` for the sampled Fourier matrix with
frequencies `ω`:  `(1 - δ) ‖x‖² ≤ ‖A x‖² ≤ (1 + δ) ‖x‖²` for every `k`-tree-sparse `x`. -/
def TreeRIP (N m k : ℕ) (δ : ℝ) (ω : Fin m → Fin N) : Prop :=
  ∀ x : Fin N → ℂ, TreeSparse N k x →
    (1 - δ) * ∑ j : Fin N, ‖x j‖ ^ 2 ≤ measNormSq N m ω x ∧
      measNormSq N m ω x ≤ (1 + δ) * ∑ j : Fin N, ‖x j‖ ^ 2

end FourierTreeRIP
