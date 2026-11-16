module

public import TreeRIP.Count

@[expose] public section

/-! # Theorem 1 and Corollary 3 -/

namespace FourierTreeRIP

/-- **Theorem 1**: optimizing the broom parameters. -/
theorem fourier_tree_rip_lower_bound_aux (N k m : ℕ) (hm : 0 < m)
    (hmk : (20000 : ℝ) * m ≤ k * min (k : ℝ) (Real.logb 2 ((N : ℝ) / k))) :
    2 * {ω : Fin m → Fin N | TreeRIP N m k (1 / 4) ω}.ncard ≤ N ^ m := by
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨L, hL⟩ : ∃ L, L = Real.logb 2 ((N : ℝ) / k) := ⟨_, rfl⟩
  rw [← hL] at hmk
  have hkr0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk8 : 8 ≤ k := by
    by_contra hc
    have hk7 : (k : ℝ) ≤ 7 := by
      have : k ≤ 7 := by omega
      exact_mod_cast this
    have : (k : ℝ) * min (k : ℝ) L ≤ 49 := by
      calc (k : ℝ) * min (k : ℝ) L ≤ k * k :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hkr0
        _ ≤ 49 := by nlinarith
    linarith
  have hk8r : (8 : ℝ) ≤ k := by exact_mod_cast hk8
  have hkpos : (0 : ℝ) < k := by linarith
  have hminpos : 0 < min (k : ℝ) L := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith
  have hLpos : 0 < L := lt_of_lt_of_le hminpos (min_le_right _ _)
  have hNk : k < N := by
    by_contra hc
    have hle : (N : ℝ) / k ≤ 1 := by
      rw [div_le_one hkpos]
      exact_mod_cast (not_lt.1 hc)
    have : L ≤ 0 := by
      rw [hL]
      exact Real.logb_nonpos (by norm_num) (by positivity) hle
    linarith
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  -- the bush size `a = 2 ^ r`, with `8 a ≤ k < 16 a`
  obtain ⟨r, hr⟩ : ∃ r, r = Nat.log 2 (k / 8) := ⟨_, rfl⟩
  have hk8' : k / 8 ≠ 0 := by omega
  have ha1 : 2 ^ r ≤ k / 8 := by rw [hr]; exact Nat.pow_log_le_self 2 hk8'
  have ha2 : k / 8 < 2 ^ (r + 1) := by
    rw [hr]; exact Nat.lt_pow_succ_log_self (by norm_num) _
  have ha2' : k / 8 < 2 * 2 ^ r := by
    have e : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
    rwa [e] at ha2
  have ha3 : 8 * 2 ^ r ≤ k := by omega
  have ha4 : k < 16 * 2 ^ r := by omega
  have hapos : 0 < 2 ^ r := by positivity
  -- the stem height
  obtain ⟨L0, hL0⟩ : ∃ L0, L0 = Nat.log 2 (N / (3 * 2 ^ r)) := ⟨_, rfl⟩
  have h3a : 0 < 3 * 2 ^ r := by positivity
  have hdiv : N / (3 * 2 ^ r) ≠ 0 := by
    have : 3 * 2 ^ r ≤ N := by omega
    exact (Nat.div_pos this h3a).ne'
  have hL0a : 2 ^ L0 ≤ N / (3 * 2 ^ r) := by rw [hL0]; exact Nat.pow_log_le_self 2 hdiv
  have hL0b : N / (3 * 2 ^ r) < 2 ^ (L0 + 1) := by
    rw [hL0]; exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hL0a' : 3 * 2 ^ r * 2 ^ L0 ≤ N := by
    have := (Nat.le_div_iff_mul_le h3a).1 hL0a
    calc 3 * 2 ^ r * 2 ^ L0 = 2 ^ L0 * (3 * 2 ^ r) := by ring
      _ ≤ N := this
  have hL0b' : N < 2 ^ (L0 + 1) * (3 * 2 ^ r) := (Nat.div_lt_iff_lt_mul h3a).1 hL0b
  obtain ⟨h, hh⟩ : ∃ h, h = max 1 (min (k / 2) L0) := ⟨_, rfl⟩
  have hh1 : 1 ≤ h := by rw [hh]; exact le_max_left _ _
  have hhk : h ≤ k / 2 := by rw [hh]; exact max_le (by omega) (min_le_left _ _)
  have H1 : h + 3 * 2 ^ r ≤ k := by omega
  have H2 : 2 ^ r * (2 * 2 ^ h + 1) ≤ N := by
    rcases le_or_gt (min (k / 2) L0) 1 with hc | hc
    · have he : h = 1 := by rw [hh]; exact max_eq_left hc
      rw [he]
      norm_num
      omega
    · have hhe : h = min (k / 2) L0 := by rw [hh]; exact max_eq_right hc.le
      have hle : h ≤ L0 := by rw [hhe]; exact min_le_right _ _
      have hp : 2 ^ h ≤ 2 ^ L0 := Nat.pow_le_pow_right (by norm_num) hle
      have h1' : 1 ≤ 2 ^ h := Nat.one_le_two_pow
      calc 2 ^ r * (2 * 2 ^ h + 1) ≤ 2 ^ r * (3 * 2 ^ h) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ 2 ^ r * (3 * 2 ^ L0) := Nat.mul_le_mul_left _ (by omega)
        _ = 3 * 2 ^ r * 2 ^ L0 := by ring
        _ ≤ N := hL0a'
  have hLle : L ≤ (L0 : ℝ) + 2 := by
    have c1 : (N : ℝ) ≤ (2 : ℝ) ^ (L0 + 1) * (3 * 2 ^ r) := by exact_mod_cast hL0b'.le
    have c2 : (8 : ℝ) * 2 ^ r ≤ k := by exact_mod_cast ha3
    have c3 : (0 : ℝ) < (2 : ℝ) ^ (L0 + 1) := by positivity
    have c4 : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
    have hlt : (N : ℝ) / k ≤ (2 : ℝ) ^ (L0 + 2) := by
      rw [div_le_iff₀ hkpos]
      calc (N : ℝ) ≤ (2 : ℝ) ^ (L0 + 1) * (3 * 2 ^ r) := c1
        _ ≤ (2 : ℝ) ^ (L0 + 1) * (2 * k) := by
            apply mul_le_mul_of_nonneg_left _ c3.le
            linarith
        _ = (2 : ℝ) ^ (L0 + 2) * k := by ring
    have hpos : (0 : ℝ) < (N : ℝ) / k := div_pos hNpos hkpos
    calc L = Real.logb 2 ((N : ℝ) / k) := hL
      _ ≤ Real.logb 2 ((2 : ℝ) ^ (L0 + 2)) :=
          Real.logb_le_logb_of_le (by norm_num) hpos hlt
      _ = (L0 : ℝ) + 2 := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
          push_cast
          ring
  have hhr : min (k : ℝ) L ≤ 4 * h := by
    have hk2 : (k : ℝ) ≤ 4 * ((k / 2 : ℕ) : ℝ) := by
      have : k ≤ 4 * (k / 2) := by omega
      exact_mod_cast this
    rcases le_or_gt (min (k / 2) L0) 1 with hc | hc
    · have he : h = 1 := by rw [hh]; exact max_eq_left hc
      have hL01 : L0 ≤ 1 := by
        rcases min_le_iff.1 hc with h' | h'
        · omega
        · exact h'
      have hL01r : (L0 : ℝ) ≤ 1 := by exact_mod_cast hL01
      rw [he]
      push_cast
      exact (min_le_right _ _).trans (by linarith)
    · have hhe : h = min (k / 2) L0 := by rw [hh]; exact max_eq_right hc.le
      have hL02 : 2 ≤ L0 := by
        have := lt_min_iff.1 hc
        omega
      rcases le_total (k / 2) L0 with h' | h'
      · have he : h = k / 2 := by rw [hhe]; exact min_eq_left h'
        rw [he]
        exact (min_le_left _ _).trans hk2
      · have he : h = L0 := by rw [hhe]; exact min_eq_right h'
        rw [he]
        have : (2 : ℝ) ≤ L0 := by exact_mod_cast hL02
        exact (min_le_right _ _).trans (by linarith)
  have H3 : 272 * m ≤ 2 ^ r * h := by
    have c4 : (k : ℝ) ≤ 16 * 2 ^ r := by exact_mod_cast ha4.le
    have hhr0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    have c5 : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
    have s1 : (k : ℝ) * min (k : ℝ) L ≤ (16 * 2 ^ r) * (4 * h) :=
      mul_le_mul c4 hhr hminpos.le (by positivity)
    have s2 : (0 : ℝ) ≤ (2 : ℝ) ^ r * h := by positivity
    have : (272 : ℝ) * m ≤ (2 : ℝ) ^ r * h := by nlinarith
    exact_mod_cast this
  exact broom_lower_bound_aux N m k r h H1 H2 H3

/-- **Corollary 3**: the quadratic regime. -/
theorem fourier_tree_rip_quadratic_aux (N k m : ℕ) (hm : 0 < m) (hN : k * 2 ^ k ≤ N)
    (hmk : 20000 * m ≤ k ^ 2) :
    2 * {ω : Fin m → Fin N | TreeRIP N m k (1 / 4) ω}.ncard ≤ N ^ m := by
  refine fourier_tree_rip_lower_bound_aux N k m hm ?_
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp at hmk; omega
    · exact h0
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : (k : ℝ) ≤ Real.logb 2 ((N : ℝ) / k) := by
    have hle : (2 : ℝ) ^ k ≤ (N : ℝ) / k := by
      rw [le_div_iff₀ hkr]
      have : (2 : ℝ) ^ k * k = ((k * 2 ^ k : ℕ) : ℝ) := by push_cast; ring
      rw [this]
      exact_mod_cast hN
    calc (k : ℝ) = Real.logb 2 ((2 : ℝ) ^ k) := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
      _ ≤ Real.logb 2 ((N : ℝ) / k) :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) hle
  rw [min_eq_left h1]
  have : ((20000 * m : ℕ) : ℝ) ≤ ((k ^ 2 : ℕ) : ℝ) := by exact_mod_cast hmk
  push_cast at this
  nlinarith

end FourierTreeRIP
