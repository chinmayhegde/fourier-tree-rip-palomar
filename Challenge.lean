module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# A quadratic lower bound for Fourier RIP with tree-structured sparsity

Statements only.  Coordinates `1, 2, …, N - 1` are the nodes of the canonical binary heap:
node `j` has children `2 j` and `2 j + 1`, i.e. the parent of `j ≥ 2` is `j / 2`, and `1`
is the root.  (Coordinate `0` is not a node of the tree.)
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


/-- **Proposition 2** (broom lower bound, explicit constants).  Let `a = 2 ^ r`.  If a broom
with stem height `h` and bush size `a` fits in the tree budget (`h + 3 a ≤ k`) and in the
index range (`a (2 · 2^h + 1) ≤ N`), and `272 m ≤ a h`, then for at least half of all
`N ^ m` choices of the `m` sampled frequencies, tree-RIP of order `k` with constant `1/4`
fails. -/
theorem broom_lower_bound (N m k r h : ℕ) (hk : h + 3 * 2 ^ r ≤ k)
    (hN : 2 ^ r * (2 * 2 ^ h + 1) ≤ N) (hm : 272 * m ≤ 2 ^ r * h) :
    2 * {ω : Fin m → Fin N | TreeRIP N m k (1 / 4) ω}.ncard ≤ N ^ m := sorry

/-- **Theorem 1** (Fourier tree-RIP lower bound).  If
`m ≤ (1 / 20000) · k · min (k, log₂ (N / k))`, then for at least half of all `N ^ m`
choices of the `m` sampled frequencies (i.e. with probability `≥ 1/2` under i.i.d. uniform
sampling), tree-RIP of order `k` with constant `1/4` fails. -/
theorem fourier_tree_rip_lower_bound (N k m : ℕ) (hm : 0 < m)
    (hmk : (20000 : ℝ) * m ≤ k * min (k : ℝ) (Real.logb 2 ((N : ℝ) / k))) :
    2 * {ω : Fin m → Fin N | TreeRIP N m k (1 / 4) ω}.ncard ≤ N ^ m := sorry

/-- **Corollary 3** (quadratic regime).  If `N ≥ k 2^k` and `m ≤ k² / 20000`, tree-RIP of
order `k` with constant `1/4` fails for at least half of all frequency choices. -/
theorem fourier_tree_rip_quadratic (N k m : ℕ) (hm : 0 < m) (hN : k * 2 ^ k ≤ N)
    (hmk : 20000 * m ≤ k ^ 2) :
    2 * {ω : Fin m → Fin N | TreeRIP N m k (1 / 4) ω}.ncard ≤ N ^ m := sorry

/-- **Sanity check on the definitions (Parseval).**  Sampling every frequency exactly once
(`m = N`, `ω = id`) is an exact isometry, so `measNormSq` has the intended normalization. -/
theorem full_dft_isometry (N : ℕ) (hN : 0 < N) (x : Fin N → ℂ) :
    measNormSq N N (fun ℓ => ℓ) x = ∑ j : Fin N, ‖x j‖ ^ 2 := sorry

/-- **Sanity check on the definitions.**  The full DFT satisfies tree-RIP of every order
with constant `0`; in particular `TreeRIP` is satisfiable and the lower bounds above are
not vacuous. -/
theorem treeRIP_full_dft (N k : ℕ) (hN : 0 < N) : TreeRIP N N k 0 (fun ℓ => ℓ) := sorry

end FourierTreeRIP
