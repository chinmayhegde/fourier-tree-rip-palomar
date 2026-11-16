module

public import TreeRIP.Main
public import TreeRIP.Sanity

public section

/-! Bridge file: the challenge theorems, proved from the `TreeRIP` library. -/

namespace FourierTreeRIP

/-- **Proposition 2** (broom lower bound, explicit constants).  Let `a = 2 ^ r`.  If a broom
with stem height `h` and bush size `a` fits in the tree budget (`h + 3 a ≤ k`) and in the
index range (`a (2 · 2^h + 1) ≤ N`), and `272 m ≤ a h`, then for at least half of all
`N ^ m` choices of the `m` sampled frequencies, tree-RIP of order `k` with constant `1/4`
fails. -/
theorem broom_lower_bound (N m k r h : ℕ) (hk : h + 3 * 2 ^ r ≤ k)
    (hN : 2 ^ r * (2 * 2 ^ h + 1) ≤ N) (hm : 272 * m ≤ 2 ^ r * h) :
    2 * {ω : Fin m → Fin N | TreeRIP N m k (1 / 4) ω}.ncard ≤ N ^ m := 
  broom_lower_bound_aux N m k r h hk hN hm

/-- **Theorem 1** (Fourier tree-RIP lower bound).  If
`m ≤ (1 / 20000) · k · min (k, log₂ (N / k))`, then for at least half of all `N ^ m`
choices of the `m` sampled frequencies (i.e. with probability `≥ 1/2` under i.i.d. uniform
sampling), tree-RIP of order `k` with constant `1/4` fails. -/
theorem fourier_tree_rip_lower_bound (N k m : ℕ) (hm : 0 < m)
    (hmk : (20000 : ℝ) * m ≤ k * min (k : ℝ) (Real.logb 2 ((N : ℝ) / k))) :
    2 * {ω : Fin m → Fin N | TreeRIP N m k (1 / 4) ω}.ncard ≤ N ^ m := 
  fourier_tree_rip_lower_bound_aux N k m hm hmk

/-- **Corollary 3** (quadratic regime).  If `N ≥ k 2^k` and `m ≤ k² / 20000`, tree-RIP of
order `k` with constant `1/4` fails for at least half of all frequency choices. -/
theorem fourier_tree_rip_quadratic (N k m : ℕ) (hm : 0 < m) (hN : k * 2 ^ k ≤ N)
    (hmk : 20000 * m ≤ k ^ 2) :
    2 * {ω : Fin m → Fin N | TreeRIP N m k (1 / 4) ω}.ncard ≤ N ^ m := 
  fourier_tree_rip_quadratic_aux N k m hm hN hmk

/-- **Sanity check on the definitions (Parseval).**  Sampling every frequency exactly once
(`m = N`, `ω = id`) is an exact isometry, so `measNormSq` has the intended normalization. -/
theorem full_dft_isometry (N : ℕ) (hN : 0 < N) (x : Fin N → ℂ) :
    measNormSq N N (fun ℓ => ℓ) x = ∑ j : Fin N, ‖x j‖ ^ 2 := 
  full_dft_isometry_aux N hN x

/-- **Sanity check on the definitions.**  The full DFT satisfies tree-RIP of every order
with constant `0`; in particular `TreeRIP` is satisfiable and the lower bounds above are
not vacuous. -/
theorem treeRIP_full_dft (N k : ℕ) (hN : 0 < N) : TreeRIP N N k 0 (fun ℓ => ℓ) := 
  treeRIP_full_dft_aux N k hN

end FourierTreeRIP
