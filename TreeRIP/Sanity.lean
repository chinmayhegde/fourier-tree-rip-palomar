module

public import TreeRIP.Broom

public section

/-! # Sanity check on the definitions: the full DFT is an isometry (Parseval) -/

namespace FourierTreeRIP

open Finset

lemma exp_eq_root_pow' (N w j : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (w : ℂ) * (j : ℂ) / (N : ℂ)) = root N j ^ w := by
  rw [← exp_eq_root_pow]
  congr 1
  ring

lemma conj_root (N w : ℕ) :
    (starRingEnd ℂ) (root N w) = Complex.exp (-(2 * Real.pi * Complex.I * (w : ℂ) / (N : ℂ))) := by
  unfold root
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_div₀, Complex.conj_I, Complex.conj_ofReal, map_natCast, map_ofNat]
  ring

/-- Orthogonality of the characters of `ℤ / N`. -/
lemma sum_root_orthogonal {N : ℕ} (hN : 0 < N) {j j' : ℕ} (hj : j < N) (hj' : j' < N) :
    ∑ ℓ ∈ range N, root N j ^ ℓ * (starRingEnd ℂ) (root N j' ^ ℓ)
      = if j = j' then (N : ℂ) else 0 := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = root N j * (starRingEnd ℂ) (root N j') := ⟨_, rfl⟩
  have hpow : ∀ ℓ : ℕ, root N j ^ ℓ * (starRingEnd ℂ) (root N j' ^ ℓ) = ρ ^ ℓ := by
    intro ℓ
    rw [map_pow, ← mul_pow, hρdef]
  simp_rw [hpow]
  have hρ : ρ = Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) - (j' : ℂ)) / (N : ℂ)) := by
    rw [hρdef, conj_root]
    unfold root
    rw [← Complex.exp_add]
    congr 1
    ring
  split_ifs with h
  · subst h
    have : ρ = 1 := by rw [hρ]; simp
    rw [this]
    simp
  · have hN1 : ρ ^ N = 1 := by
      rw [hρ, ← Complex.exp_nat_mul]
      have : (N : ℂ) * (2 * Real.pi * Complex.I * ((j : ℂ) - (j' : ℂ)) / (N : ℂ))
          = (((j : ℤ) - (j' : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    have hne : ρ ≠ 1 := by
      rw [hρ]
      intro h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
      have hd : ((j : ℂ) - (j' : ℂ)) = (n : ℂ) * (N : ℂ) := by
        have e : (2 * Real.pi * Complex.I : ℂ) * (((j : ℂ) - (j' : ℂ)) / (N : ℂ))
            = (2 * Real.pi * Complex.I : ℂ) * (n : ℂ) := by
          rw [← hn.symm.symm.trans (mul_comm _ _)]
          ring
        have := mul_left_cancel₀ hpi e
        rw [div_eq_iff hNc] at this
        exact this
      have hd' : (j : ℤ) - (j' : ℤ) = n * (N : ℤ) := by exact_mod_cast hd
      have hNz : (0 : ℤ) < N := by exact_mod_cast hN
      have hjz : (j : ℤ) < N := by exact_mod_cast hj
      have hjz' : (j' : ℤ) < N := by exact_mod_cast hj'
      have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
      have hj0' : (0 : ℤ) ≤ j' := Int.natCast_nonneg j'
      rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
      · nlinarith
      · rw [hn0, zero_mul] at hd'
        apply h
        omega
      · nlinarith
    have hg := geom_sum_mul ρ N
    rw [hN1, sub_self] at hg
    exact (mul_eq_zero.1 hg).resolve_right (sub_ne_zero.2 hne)

/-- **Sanity check (Parseval).**  Sampling every frequency exactly once (`m = N`, `ω = id`)
gives an exact isometry, so the normalization of `measNormSq` is the intended one. -/
theorem full_dft_isometry_aux (N : ℕ) (hN : 0 < N) (x : Fin N → ℂ) :
    measNormSq N N (fun ℓ => ℓ) x = ∑ j : Fin N, ‖x j‖ ^ 2 := by
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have key : ∀ ℓ : Fin N, ((‖∑ j : Fin N, x j * Complex.exp (2 * Real.pi * Complex.I *
      ((ℓ : ℕ) : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ))‖ ^ 2 : ℝ) : ℂ)
      = ∑ j : Fin N, ∑ j' : Fin N, x j * (starRingEnd ℂ) (x j') *
          (root N j ^ (ℓ : ℕ) * (starRingEnd ℂ) (root N j' ^ (ℓ : ℕ))) := by
    intro ℓ
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine sum_congr rfl fun j _ => sum_congr rfl fun j' _ => ?_
    rw [exp_eq_root_pow', exp_eq_root_pow', map_mul]
    ring
  have hsum : ((∑ ℓ : Fin N, ‖∑ j : Fin N, x j * Complex.exp (2 * Real.pi * Complex.I *
      ((ℓ : ℕ) : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ))‖ ^ 2 : ℝ) : ℂ)
      = (((N : ℝ) * ∑ j : Fin N, ‖x j‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp_rw [key]
    rw [sum_comm]
    have inner : ∀ j : Fin N, ∑ ℓ : Fin N, ∑ j' : Fin N, x j * (starRingEnd ℂ) (x j') *
          (root N j ^ (ℓ : ℕ) * (starRingEnd ℂ) (root N j' ^ (ℓ : ℕ)))
        = (N : ℂ) * ((‖x j‖ ^ 2 : ℝ) : ℂ) := by
      intro j
      rw [sum_comm]
      have h2 : ∀ j' : Fin N, ∑ ℓ : Fin N, x j * (starRingEnd ℂ) (x j') *
            (root N j ^ (ℓ : ℕ) * (starRingEnd ℂ) (root N j' ^ (ℓ : ℕ)))
          = if j = j' then x j * (starRingEnd ℂ) (x j') * (N : ℂ) else 0 := by
        intro j'
        rw [← mul_sum, Fin.sum_univ_eq_sum_range
          (fun ℓ => root N j ^ ℓ * (starRingEnd ℂ) (root N j' ^ ℓ)) N,
          sum_root_orthogonal hN j.2 j'.2]
        by_cases h : j = j'
        · simp [h]
        · have h' : (j : ℕ) ≠ (j' : ℕ) := fun e => h (Fin.ext e)
          simp [h, h']
      simp_rw [h2]
      rw [sum_ite_eq]
      simp only [mem_univ, ite_true]
      rw [Complex.ofReal_pow, ← Complex.mul_conj']
      ring
    simp_rw [inner]
    rw [← mul_sum]
    push_cast
    rfl
  have hreal : ∑ ℓ : Fin N, ‖∑ j : Fin N, x j * Complex.exp (2 * Real.pi * Complex.I *
      ((ℓ : ℕ) : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ))‖ ^ 2 = (N : ℝ) * ∑ j : Fin N, ‖x j‖ ^ 2 :=
    Complex.ofReal_injective hsum
  unfold measNormSq
  rw [hreal]
  field_simp

/-- Consequently the full DFT satisfies tree-RIP of every order with constant `0`:
the tree-RIP predicate is satisfiable, and the lower bounds are not vacuous. -/
theorem treeRIP_full_dft_aux (N k : ℕ) (hN : 0 < N) : TreeRIP N N k 0 (fun ℓ => ℓ) := by
  intro x _
  rw [full_dft_isometry_aux N hN x]
  constructor <;> simp

end FourierTreeRIP
