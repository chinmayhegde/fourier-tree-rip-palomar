module

public import TreeRIP.Defs
public import TreeRIP.Kernel
public import TreeRIP.Tree
public import TreeRIP.Dirichlet

@[expose] public section

/-! # Deterministic core: few main-lobe samples + small tail mass ⇒ tree-RIP fails -/

namespace FourierTreeRIP

open Finset

lemma exp_eq_root_pow (N w j : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (w : ℂ) * (j : ℂ) / (N : ℂ)) = root N w ^ j := by
  unfold root
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

lemma root_pow_mul (N w a n : ℕ) :
    root N w ^ (a * n) = Complex.exp (2 * Real.pi * Complex.I *
      ((((a * w : ℕ) : ℝ) / (N : ℝ) : ℝ) : ℂ) * (n : ℂ)) := by
  unfold root
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma measNormSq_eq (N m : ℕ) (ω : Fin m → Fin N) (f : ℕ → ℂ) :
    measNormSq N m ω (fun j : Fin N => f j)
      = 1 / (m : ℝ) * ∑ ℓ : Fin m, ‖∑ j ∈ range N, f j * root N (ω ℓ) ^ j‖ ^ 2 := by
  unfold measNormSq
  congr 1
  refine sum_congr rfl fun ℓ _ => ?_
  congr 2
  rw [← Fin.sum_univ_eq_sum_range (fun j => f j * root N (ω ℓ) ^ j) N]
  refine sum_congr rfl fun j _ => ?_
  rw [exp_eq_root_pow]

/-- Indicator of the interval `[b, b + a)`. -/
noncomputable def ind (b a j : ℕ) : ℂ := if b ≤ j ∧ j < b + a then 1 else 0

lemma filter_range_eq_Ico {N b a : ℕ} (hb : b + a ≤ N) :
    (range N).filter (fun j => b ≤ j ∧ j < b + a) = Ico b (b + a) := by
  ext j
  simp only [mem_filter, mem_range, mem_Ico]
  omega

lemma sum_ind_mul {N b a : ℕ} (hb : b + a ≤ N) (z : ℂ) :
    ∑ j ∈ range N, ind b a j * z ^ j = z ^ b * ∑ i ∈ range a, z ^ i := by
  unfold ind
  simp only [ite_mul, one_mul, zero_mul]
  rw [← sum_filter, filter_range_eq_Ico hb, sum_Ico_eq_sum_range, mul_sum]
  refine sum_congr (by simp) fun i _ => ?_
  rw [pow_add]

lemma measNormSq_ind {N m b a : ℕ} (hb : b + a ≤ N) (ω : Fin m → Fin N) :
    measNormSq N m ω (fun j : Fin N => ind b a j)
      = 1 / (m : ℝ) * ∑ ℓ : Fin m, ‖dir N a (ω ℓ)‖ ^ 2 := by
  rw [measNormSq_eq]
  congr 1
  refine sum_congr rfl fun ℓ _ => ?_
  rw [sum_ind_mul hb, norm_mul, norm_root_pow, one_mul]
  rfl

lemma measNormSq_ind_sub {N m b a : ℕ} (hb : 2 * b + a ≤ N) (ω : Fin m → Fin N) :
    measNormSq N m ω (fun j : Fin N => ind (2 * b) a j - ind b a j)
      = 1 / (m : ℝ) * ∑ ℓ : Fin m, ‖root N (ω ℓ) ^ b - 1‖ ^ 2 * ‖dir N a (ω ℓ)‖ ^ 2 := by
  have := measNormSq_eq N m ω (fun j => ind (2 * b) a j - ind b a j)
  rw [this]
  congr 1
  refine sum_congr rfl fun ℓ _ => ?_
  have e : ∑ j ∈ range N, (ind (2 * b) a j - ind b a j) * root N (ω ℓ) ^ j
      = root N (ω ℓ) ^ b * ((root N (ω ℓ) ^ b - 1) * dir N a (ω ℓ)) := by
    simp only [sub_mul, sum_sub_distrib]
    rw [sum_ind_mul hb, sum_ind_mul (by omega : b + a ≤ N)]
    unfold dir
    ring
  rw [e, norm_mul, norm_root_pow, one_mul, norm_mul, mul_pow]

lemma sum_fin_boole_Ico {N b a : ℕ} (hb : b + a ≤ N) :
    ∑ j : Fin N, (if b ≤ (j : ℕ) ∧ (j : ℕ) < b + a then (1 : ℝ) else 0) = a := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if b ≤ j ∧ j < b + a then (1 : ℝ) else 0) N,
    sum_boole, filter_range_eq_Ico hb, Nat.card_Ico]
  simp

lemma normSq_ind {N b a : ℕ} (hb : b + a ≤ N) :
    ∑ j : Fin N, ‖ind b a j‖ ^ 2 = a := by
  rw [← sum_fin_boole_Ico hb]
  refine sum_congr rfl fun j _ => ?_
  unfold ind
  split_ifs <;> simp

lemma normSq_ind_sub {N b a : ℕ} (hb : 2 * b + a ≤ N) (hab : a ≤ b) :
    ∑ j : Fin N, ‖ind (2 * b) a j - ind b a j‖ ^ 2 = 2 * a := by
  have h1 := sum_fin_boole_Ico (N := N) (b := 2 * b) (a := a) hb
  have h2 := sum_fin_boole_Ico (N := N) (b := b) (a := a) (by omega)
  have : (2 : ℝ) * a = ∑ j : Fin N,
      ((if 2 * b ≤ (j : ℕ) ∧ (j : ℕ) < 2 * b + a then (1 : ℝ) else 0)
        + (if b ≤ (j : ℕ) ∧ (j : ℕ) < b + a then (1 : ℝ) else 0)) := by
    rw [sum_add_distrib, h1, h2]; ring
  rw [this]
  refine sum_congr rfl fun j _ => ?_
  unfold ind
  split_ifs <;> first | (exfalso; omega) | simp

/-- If few samples land in the main lobe and the off-lobe kernel mass is small,
tree-RIP with constant `1/4` fails. -/
lemma not_treeRIP_of_good {N m k r h M : ℕ} (hk : h + 3 * 2 ^ r ≤ k)
    (hN : 2 ^ r * (2 * 2 ^ h + 1) ≤ N) (ω : Fin m → Fin N)
    (hq : 4 * (univ.filter
      (fun ℓ : Fin m => ¬ (M < (ω ℓ : ℕ) ∧ (ω ℓ : ℕ) + M < N))).card ≤ h)
    (hout : 4 * ∑ ℓ : Fin m, (if M < (ω ℓ : ℕ) ∧ (ω ℓ : ℕ) + M < N
      then ‖dir N (2 ^ r) (ω ℓ)‖ ^ 2 else 0) ≤ (2 : ℝ) ^ r * m) :
    ¬ TreeRIP N m k (1 / 4) ω := by
  intro hrip
  classical
  set J := univ.filter (fun ℓ : Fin m => ¬ (M < (ω ℓ : ℕ) ∧ (ω ℓ : ℕ) + M < N)) with hJ
  obtain ⟨n, hn1, hn2, happ⟩ := exists_simultaneous_approx (ι := J)
    (fun ℓ => ((2 ^ r * (ω ℓ.1 : ℕ) : ℕ) : ℝ) / (N : ℝ))
  have hnh : n ≤ 2 ^ h := by
    calc n ≤ 16 ^ Fintype.card J := hn2
      _ = 2 ^ (4 * J.card) := by rw [Fintype.card_coe, pow_mul]; norm_num
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hq
  have hb : 2 * (2 ^ r * n) + 2 ^ r ≤ N := by
    calc 2 * (2 ^ r * n) + 2 ^ r = 2 ^ r * (2 * n + 1) := by ring
      _ ≤ 2 ^ r * (2 * 2 ^ h + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ N := hN
  have hab : 2 ^ r ≤ 2 ^ r * n := Nat.le_mul_of_pos_right _ hn1
  have happ' : ∀ ℓ : Fin m, ¬ (M < (ω ℓ : ℕ) ∧ (ω ℓ : ℕ) + M < N) →
      ‖root N (ω ℓ) ^ (2 ^ r * n) - 1‖ ≤ 1 / 2 := by
    intro ℓ hℓ
    have hmem : ℓ ∈ J := by rw [hJ]; exact mem_filter.2 ⟨mem_univ _, hℓ⟩
    have := happ ⟨ℓ, hmem⟩
    rw [root_pow_mul]
    exact this
  have hsub : IsRootedSubtree (broom r h n) := broom_isRootedSubtree hn1 hnh
  have hcard : (broom r h n).card ≤ k := (broom_card_le r h n).trans hk
  -- the two test vectors
  have hv := (hrip (fun j : Fin N => ind (2 ^ r * n) (2 ^ r) j) ⟨broom r h n, hsub, hcard, by
    intro j hj
    by_cases hc : 2 ^ r * n ≤ (j : ℕ) ∧ (j : ℕ) < 2 ^ r * n + 2 ^ r
    · exact lower_mem_broom hc.1 hc.2
    · exact absurd (by simp [ind, hc]) hj⟩).2
  have hw := (hrip (fun j : Fin N => ind (2 * (2 ^ r * n)) (2 ^ r) j - ind (2 ^ r * n) (2 ^ r) j)
    ⟨broom r h n, hsub, hcard, by
      intro j hj
      by_cases hc : 2 ^ r * n ≤ (j : ℕ) ∧ (j : ℕ) < 2 ^ r * n + 2 ^ r
      · exact lower_mem_broom hc.1 hc.2
      · by_cases hc' : 2 * (2 ^ r * n) ≤ (j : ℕ) ∧ (j : ℕ) < 2 * (2 ^ r * n) + 2 ^ r
        · exact upper_mem_broom hc'.1 hc'.2
        · exact absurd (by simp [ind, hc, hc']) hj⟩).1
  rw [measNormSq_ind (by omega), normSq_ind (by omega)] at hv
  rw [measNormSq_ind_sub hb, normSq_ind_sub hb hab] at hw
  -- pointwise comparison
  have hpt : ∀ ℓ : Fin m, ‖root N (ω ℓ) ^ (2 ^ r * n) - 1‖ ^ 2 * ‖dir N (2 ^ r) (ω ℓ)‖ ^ 2
      ≤ 1 / 4 * ‖dir N (2 ^ r) (ω ℓ)‖ ^ 2
        + 4 * (if M < (ω ℓ : ℕ) ∧ (ω ℓ : ℕ) + M < N
            then ‖dir N (2 ^ r) (ω ℓ)‖ ^ 2 else 0) := by
    intro ℓ
    have hP : 0 ≤ ‖dir N (2 ^ r) (ω ℓ)‖ ^ 2 := by positivity
    have h0 : 0 ≤ ‖root N (ω ℓ) ^ (2 ^ r * n) - 1‖ := norm_nonneg _
    by_cases hc : M < (ω ℓ : ℕ) ∧ (ω ℓ : ℕ) + M < N
    · simp only [hc, and_self, ite_true]
      have h2 := norm_root_pow_sub_one_le N (ω ℓ) (2 ^ r * n)
      have : ‖root N (ω ℓ) ^ (2 ^ r * n) - 1‖ ^ 2 ≤ 4 := by nlinarith
      nlinarith
    · simp only [hc, ite_false]
      have h2 := happ' ℓ hc
      have : ‖root N (ω ℓ) ^ (2 ^ r * n) - 1‖ ^ 2 ≤ 1 / 4 := by nlinarith
      nlinarith
  have hsum : ∑ ℓ : Fin m, ‖root N (ω ℓ) ^ (2 ^ r * n) - 1‖ ^ 2 * ‖dir N (2 ^ r) (ω ℓ)‖ ^ 2
      ≤ 1 / 4 * ∑ ℓ : Fin m, ‖dir N (2 ^ r) (ω ℓ)‖ ^ 2
        + 4 * ∑ ℓ : Fin m, (if M < (ω ℓ : ℕ) ∧ (ω ℓ : ℕ) + M < N
            then ‖dir N (2 ^ r) (ω ℓ)‖ ^ 2 else 0) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun ℓ _ => hpt ℓ
  generalize (∑ ℓ : Fin m, ‖root N (ω ℓ) ^ (2 ^ r * n) - 1‖ ^ 2 * ‖dir N (2 ^ r) (ω ℓ)‖ ^ 2)
    = S2 at hw hsum
  generalize (∑ ℓ : Fin m, ‖dir N (2 ^ r) (ω ℓ)‖ ^ 2) = S1 at hv hsum
  generalize (∑ ℓ : Fin m, (if M < (ω ℓ : ℕ) ∧ (ω ℓ : ℕ) + M < N
            then ‖dir N (2 ^ r) (ω ℓ)‖ ^ 2 else 0)) = S3 at hout hsum
  have hA : (0 : ℝ) < ((2 ^ r : ℕ) : ℝ) := by positivity
  have ht : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  have htm : 1 / (m : ℝ) * m ≤ 1 := by
    rcases eq_or_ne (m : ℝ) 0 with h0 | h0
    · simp [h0]
    · rw [one_div_mul_cancel h0]
  have hS2 : S2 ≤ 1 / 4 * S1 + (2 : ℝ) ^ r * m := by linarith
  have h1 := mul_le_mul_of_nonneg_left hS2 ht
  have e : 1 / (m : ℝ) * (1 / 4 * S1 + (2 : ℝ) ^ r * m)
      = 1 / 4 * (1 / (m : ℝ) * S1) + (2 : ℝ) ^ r * (1 / (m : ℝ) * m) := by ring
  rw [e] at h1
  have h2 : (2 : ℝ) ^ r * (1 / (m : ℝ) * m) ≤ (2 : ℝ) ^ r := by
    have : (0 : ℝ) ≤ (2 : ℝ) ^ r := by positivity
    nlinarith
  push_cast at hv hw hA
  linarith

end FourierTreeRIP
