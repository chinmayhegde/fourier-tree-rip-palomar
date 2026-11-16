module

public import TreeRIP.Broom

public section

/-! # Counting over all `N ^ m` frequency tuples: Proposition 2 -/

namespace FourierTreeRIP

open Finset

/-- Averaging a function of one coordinate over all tuples. -/
lemma sum_pi_eval {N m : ℕ} (hN : 0 < N) (g : Fin N → ℝ) (ℓ : Fin m) :
    ∑ ω : Fin m → Fin N, g (ω ℓ) = (N : ℝ) ^ m * ((∑ x, g x) / N) := by
  classical
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have h1 : ∀ ω : Fin m → Fin N, g (ω ℓ) = ∏ i, (if i = ℓ then g (ω i) else 1) := by
    intro ω
    rw [Finset.prod_ite_eq']
    simp
  simp_rw [h1]
  have h2 := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset (Fin N)))
    (fun i x => if i = ℓ then g x else (1 : ℝ))
  rw [Fintype.piFinset_univ] at h2
  rw [← h2]
  have h3 : ∀ i : Fin m, ∑ x : Fin N, (if i = ℓ then g x else (1 : ℝ))
      = (N : ℝ) * (if i = ℓ then (∑ x, g x) / N else 1) := by
    intro i
    split_ifs with h
    · field_simp
    · simp
  simp_rw [h3]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_ite_eq']
  simp

lemma sum_pi_sum_eval {N m : ℕ} (hN : 0 < N) (g : Fin N → ℝ) :
    ∑ ω : Fin m → Fin N, ∑ ℓ : Fin m, g (ω ℓ) = m * ((N : ℝ) ^ m * ((∑ x, g x) / N)) := by
  rw [sum_comm]
  simp_rw [sum_pi_eval hN g]
  simp

lemma markov_card {Ω : Type*} [Fintype Ω] (B : Finset Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω)
    (t : ℝ) (hB : ∀ ω ∈ B, t ≤ f ω) : t * B.card ≤ ∑ ω, f ω := by
  calc t * B.card = ∑ _ω ∈ B, t := by rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ ω ∈ B, f ω := sum_le_sum hB
    _ ≤ ∑ ω, f ω := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun ω _ _ => hf ω)

/-- **Proposition 2** (broom lower bound) with explicit constants. -/
theorem broom_lower_bound_aux (N m k r h : ℕ) (hk : h + 3 * 2 ^ r ≤ k)
    (hN : 2 ^ r * (2 * 2 ^ h + 1) ≤ N) (hm : 272 * m ≤ 2 ^ r * h) :
    2 * {ω : Fin m → Fin N | TreeRIP N m k (1 / 4) ω}.ncard ≤ N ^ m := by
  classical
  have ha : 0 < 2 ^ r := by positivity
  have h2h : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  have hN3 : 3 * 2 ^ r ≤ N := by
    calc 3 * 2 ^ r = 2 ^ r * (2 * 1 + 1) := by ring
      _ ≤ 2 ^ r * (2 * 2 ^ h + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ N := hN
  have hNpos : 0 < N := by omega
  obtain ⟨M, hMdef⟩ : ∃ M, M = 8 * N / 2 ^ r + 1 := ⟨_, rfl⟩
  have hM : 0 < M := by rw [hMdef]; exact Nat.succ_pos _
  have haM : 8 * N < 2 ^ r * M := by
    rw [hMdef]; exact Nat.lt_mul_div_succ _ ha
  have haM' : 2 ^ r * (2 * M + 1) ≤ 17 * N := by
    have := Nat.mul_div_le (8 * N) (2 ^ r)
    have e : 2 ^ r * (2 * M + 1) = 2 * (2 ^ r * (8 * N / 2 ^ r)) + 3 * 2 ^ r := by
      rw [hMdef]; ring
    omega
  have key1 : 16 * m * (2 * M + 1) ≤ N * (h + 1) := by
    refine Nat.le_of_mul_le_mul_left ?_ ha
    calc 2 ^ r * (16 * m * (2 * M + 1)) = 16 * m * (2 ^ r * (2 * M + 1)) := by ring
      _ ≤ 16 * m * (17 * N) := Nat.mul_le_mul_left _ haM'
      _ = 272 * m * N := by ring
      _ ≤ 2 ^ r * h * N := Nat.mul_le_mul_right _ hm
      _ ≤ 2 ^ r * (N * (h + 1)) := by
          have : 2 ^ r * h * N = 2 ^ r * (N * h) := by ring
          rw [this]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  -- per-sample functions
  let g1 : Fin N → ℝ := fun x => if ¬ (M < (x : ℕ) ∧ (x : ℕ) + M < N) then 1 else 0
  let g2 : Fin N → ℝ := fun x => if M < (x : ℕ) ∧ (x : ℕ) + M < N
    then ‖dir N (2 ^ r) x‖ ^ 2 else 0
  have hg1 : ∀ x, 0 ≤ g1 x := fun x => by simp only [g1]; split_ifs <;> norm_num
  have hg2 : ∀ x, 0 ≤ g2 x := fun x => by simp only [g2]; split_ifs <;> positivity
  have hG1 : ∑ x, g1 x ≤ 2 * M + 1 := by
    simp only [g1]
    rw [Fin.sum_univ_eq_sum_range
      (fun w => if ¬ (M < w ∧ w + M < N) then (1 : ℝ) else 0) N, sum_boole]
    exact_mod_cast card_lobe_le N M
  have hG2 : ∑ x, g2 x ≤ (N : ℝ) ^ 2 / (2 * M) := by
    simp only [g2]
    rw [Fin.sum_univ_eq_sum_range
      (fun w => if M < w ∧ w + M < N then ‖dir N (2 ^ r) w‖ ^ 2 else 0) N, ← sum_filter]
    exact sum_tail_dir_sq N (2 ^ r) M hM
  -- the two bad events
  let B1 : Finset (Fin m → Fin N) := univ.filter (fun ω =>
    h < 4 * (univ.filter (fun ℓ : Fin m => ¬ (M < (ω ℓ : ℕ) ∧ (ω ℓ : ℕ) + M < N))).card)
  let B2 : Finset (Fin m → Fin N) := univ.filter (fun ω =>
    (2 : ℝ) ^ r * m < 4 * ∑ ℓ : Fin m, g2 (ω ℓ))
  have hsub : {ω : Fin m → Fin N | TreeRIP N m k (1 / 4) ω} ⊆ ((B1 ∪ B2 : Finset _) : Set _) := by
    intro ω hω
    by_contra hnot
    simp only [B1, B2, coe_union, coe_filter, mem_univ, true_and, Set.mem_union,
      Set.mem_ofPred_eq, not_or, not_lt] at hnot
    exact not_treeRIP_of_good hk hN ω hnot.1 hnot.2 hω
  have hcard : {ω : Fin m → Fin N | TreeRIP N m k (1 / 4) ω}.ncard ≤ B1.card + B2.card := by
    refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
    rw [Set.ncard_coe_finset]
    exact card_union_le _ _
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNm : (0 : ℝ) < (N : ℝ) ^ m := by positivity
  -- first bad event
  have hB1 : (4 : ℝ) * B1.card ≤ (N : ℝ) ^ m := by
    have hmk := markov_card B1 (fun ω => ∑ ℓ : Fin m, g1 (ω ℓ))
      (fun ω => sum_nonneg fun ℓ _ => hg1 _) (((h : ℝ) + 1) / 4) (by
        intro ω hω
        simp only [B1, mem_filter, mem_univ, true_and] at hω
        have hq : ∑ ℓ : Fin m, g1 (ω ℓ) = ((univ.filter
            (fun ℓ : Fin m => ¬ (M < (ω ℓ : ℕ) ∧ (ω ℓ : ℕ) + M < N))).card : ℝ) := by
          simp only [g1]
          rw [sum_boole]
        rw [hq]
        have : (h : ℝ) + 1 ≤ 4 * ((univ.filter
            (fun ℓ : Fin m => ¬ (M < (ω ℓ : ℕ) ∧ (ω ℓ : ℕ) + M < N))).card : ℝ) := by
          exact_mod_cast hω
        linarith)
    rw [sum_pi_sum_eval hNpos g1] at hmk
    have hk1 : (16 : ℝ) * m * (2 * M + 1) ≤ N * (h + 1) := by exact_mod_cast key1
    have hG : (m : ℝ) * ((N : ℝ) ^ m * ((∑ x, g1 x) / N))
        ≤ (m : ℝ) * ((N : ℝ) ^ m * ((2 * M + 1) / N)) := by gcongr
    have h3 : ((h : ℝ) + 1) / 4 * B1.card ≤ (m : ℝ) * ((N : ℝ) ^ m * ((2 * M + 1) / N)) :=
      hmk.trans hG
    have h4 : (N : ℝ) * ((h : ℝ) + 1) * (4 * B1.card) ≤ 16 * m * (2 * M + 1) * (N : ℝ) ^ m := by
      have := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ 16 * N by positivity)
      have e1 : 16 * (N : ℝ) * (((h : ℝ) + 1) / 4 * B1.card)
          = (N : ℝ) * ((h : ℝ) + 1) * (4 * B1.card) := by ring
      have e2 : 16 * (N : ℝ) * ((m : ℝ) * ((N : ℝ) ^ m * ((2 * M + 1) / N)))
          = 16 * m * (2 * M + 1) * (N : ℝ) ^ m := by field_simp
      rw [e1, e2] at this
      exact this
    have h5 : (N : ℝ) * ((h : ℝ) + 1) * (4 * B1.card) ≤ (N : ℝ) * ((h : ℝ) + 1) * (N : ℝ) ^ m :=
      h4.trans (mul_le_mul_of_nonneg_right hk1 hNm.le)
    exact le_of_mul_le_mul_left h5 (by positivity)
  -- second bad event
  have hB2 : (4 : ℝ) * B2.card ≤ (N : ℝ) ^ m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      have : B2 = ∅ := by
        apply filter_eq_empty_iff.2
        intro ω _
        simp
      rw [this]
      simp
    · have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
      have hmk := markov_card B2 (fun ω => ∑ ℓ : Fin m, g2 (ω ℓ))
        (fun ω => sum_nonneg fun ℓ _ => hg2 _) ((2 : ℝ) ^ r * m / 4) (by
          intro ω hω
          simp only [B2, mem_filter, mem_univ, true_and] at hω
          linarith)
      rw [sum_pi_sum_eval hNpos g2] at hmk
      have hG : (m : ℝ) * ((N : ℝ) ^ m * ((∑ x, g2 x) / N))
          ≤ (m : ℝ) * ((N : ℝ) ^ m * ((N : ℝ) ^ 2 / (2 * M) / N)) := by gcongr
      have h3 := hmk.trans hG
      have haMr : (8 : ℝ) * N ≤ (2 : ℝ) ^ r * M := by exact_mod_cast haM.le
      -- multiply through by `8 M / m`
      have h4 : (2 : ℝ) ^ r * M * B2.card ≤ 2 * N * (N : ℝ) ^ m := by
        have := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ 4 * M / m by positivity)
        have e1 : 4 * (M : ℝ) / m * ((2 : ℝ) ^ r * m / 4 * B2.card)
            = (2 : ℝ) ^ r * M * B2.card := by field_simp
        have e2 : 4 * (M : ℝ) / m * ((m : ℝ) * ((N : ℝ) ^ m * ((N : ℝ) ^ 2 / (2 * M) / N)))
            = 2 * N * (N : ℝ) ^ m := by field_simp; ring
        rw [e1, e2] at this
        exact this
      have h5 : (8 : ℝ) * N * B2.card ≤ 2 * N * (N : ℝ) ^ m :=
        (mul_le_mul_of_nonneg_right haMr (Nat.cast_nonneg _)).trans h4
      have h6 : (2 * (N : ℝ)) * (4 * B2.card) ≤ (2 * (N : ℝ)) * (N : ℝ) ^ m := by linarith
      exact le_of_mul_le_mul_left h6 (by positivity)
  have hfin : (2 : ℝ) * ({ω : Fin m → Fin N | TreeRIP N m k (1 / 4) ω}.ncard : ℝ)
      ≤ (N : ℝ) ^ m := by
    have : ({ω : Fin m → Fin N | TreeRIP N m k (1 / 4) ω}.ncard : ℝ)
        ≤ (B1.card : ℝ) + B2.card := by exact_mod_cast hcard
    linarith
  exact_mod_cast hfin

end FourierTreeRIP
