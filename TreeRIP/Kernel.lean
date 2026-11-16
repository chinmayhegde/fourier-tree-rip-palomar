module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-! # The Dirichlet/Fejér kernel on the DFT grid: main-lobe count and tail mass -/

namespace FourierTreeRIP

open Finset

/-- `root N w = exp (2 π i w / N)`. -/
noncomputable def root (N w : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (w : ℂ) / (N : ℂ))

lemma root_eq (N w : ℕ) :
    root N w = Complex.exp (Complex.I * ((2 * Real.pi * w / N : ℝ) : ℂ)) := by
  unfold root
  congr 1
  push_cast
  ring

lemma root_eq' (N w : ℕ) :
    root N w = Complex.exp (((2 * Real.pi * w / N : ℝ) : ℂ) * Complex.I) := by
  rw [root_eq, mul_comm]

@[simp] lemma norm_root (N w : ℕ) : ‖root N w‖ = 1 := by
  rw [root_eq', Complex.norm_exp_ofReal_mul_I]

@[simp] lemma norm_root_pow (N w j : ℕ) : ‖root N w ^ j‖ = 1 := by
  rw [norm_pow, norm_root, one_pow]

lemma norm_root_pow_sub_one_le (N w j : ℕ) : ‖root N w ^ j - 1‖ ≤ 2 := by
  calc ‖root N w ^ j - 1‖ ≤ ‖root N w ^ j‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_root_pow, norm_one]; norm_num

/-- The Dirichlet kernel `∑_{j < a} ζ^j` at `ζ = root N w`. -/
noncomputable def dir (N a w : ℕ) : ℂ := ∑ j ∈ range a, root N w ^ j

lemma norm_root_sub_one (N w : ℕ) :
    ‖root N w - 1‖ = 2 * |Real.sin (Real.pi * w / N)| := by
  rw [root_eq, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 3
  ring

lemma sin_lower_left {N w : ℕ} (hN : 0 < N) (hw : 2 * w ≤ N) :
    2 * (w : ℝ) / N ≤ Real.sin (Real.pi * w / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hw' : (2 : ℝ) * w ≤ N := by exact_mod_cast hw
  have hx0 : 0 ≤ Real.pi * w / N := by positivity
  have hx1 : Real.pi * w / N ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ hN' (by norm_num)]
    nlinarith [Real.pi_pos]
  have := Real.mul_le_sin hx0 hx1
  calc 2 * (w : ℝ) / N = 2 / Real.pi * (Real.pi * w / N) := by
        field_simp
    _ ≤ _ := this

lemma sin_lower {N w : ℕ} (hN : 0 < N) (hw : w ≤ N) :
    2 * (w : ℝ) / N ≤ Real.sin (Real.pi * w / N) ∨
      2 * ((N : ℝ) - w) / N ≤ Real.sin (Real.pi * w / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases h : 2 * w ≤ N
  · exact Or.inl (sin_lower_left hN h)
  · right
    have h2 : 2 * (N - w) ≤ N := by omega
    have := sin_lower_left hN h2
    rw [Nat.cast_sub hw] at this
    have e : Real.pi * ((N : ℝ) - w) / N = Real.pi - Real.pi * w / N := by
      field_simp
    rw [e, Real.sin_pi_sub] at this
    exact this

/-- Pointwise bound on the squared Dirichlet kernel away from frequency `0`. -/
lemma dir_sq_le {N a w : ℕ} (hw0 : 0 < w) (hwN : w < N) :
    ‖dir N a w‖ ^ 2 ≤ (N : ℝ) ^ 2 / 4 * (1 / (w : ℝ) ^ 2 + 1 / ((N : ℝ) - w) ^ 2) := by
  have hN : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw0
  have hNw : (0 : ℝ) < (N : ℝ) - w := by
    have : (w : ℝ) < N := by exact_mod_cast hwN
    linarith
  have hmul : dir N a w * (root N w - 1) = root N w ^ a - 1 := by
    unfold dir
    exact geom_sum_mul _ _
  have hprod : ‖dir N a w‖ * ‖root N w - 1‖ ≤ 2 := by
    rw [← norm_mul, hmul]
    exact norm_root_pow_sub_one_le N w a
  have hD : 0 ≤ ‖dir N a w‖ := norm_nonneg _
  have key : ∀ d : ℝ, 0 < d → 2 * d / N ≤ Real.sin (Real.pi * w / N) →
      ‖dir N a w‖ ^ 2 ≤ (N : ℝ) ^ 2 / 4 * (1 / d ^ 2) := by
    intro d hd hsin
    have hs : 4 * d / N ≤ ‖root N w - 1‖ := by
      rw [norm_root_sub_one]
      have : Real.sin (Real.pi * w / N) ≤ |Real.sin (Real.pi * w / N)| := le_abs_self _
      have e : 4 * d / N = 2 * (2 * d / N) := by ring
      rw [e]
      linarith
    have h1 : ‖dir N a w‖ * (4 * d / N) ≤ 2 :=
      le_trans (mul_le_mul_of_nonneg_left hs hD) hprod
    have h2 : ‖dir N a w‖ ≤ N / (2 * d) := by
      rw [le_div_iff₀ (by positivity)]
      have : ‖dir N a w‖ * (4 * d / N) * N = ‖dir N a w‖ * (2 * d) * 2 := by
        field_simp
        ring
      nlinarith
    calc ‖dir N a w‖ ^ 2 ≤ ((N : ℝ) / (2 * d)) ^ 2 := by
          exact pow_le_pow_left₀ hD h2 2
      _ = (N : ℝ) ^ 2 / 4 * (1 / d ^ 2) := by
          field_simp
          ring
  have pos1 : 0 ≤ (N : ℝ) ^ 2 / 4 * (1 / (w : ℝ) ^ 2) := by positivity
  have pos2 : 0 ≤ (N : ℝ) ^ 2 / 4 * (1 / ((N : ℝ) - w) ^ 2) := by positivity
  rcases sin_lower hN hwN.le with h | h
  · have := key w hw' h
    rw [mul_add]; linarith
  · have := key ((N : ℝ) - w) hNw h
    rw [mul_add]; linarith

lemma inv_sq_succ_le (x : ℝ) (hx : 0 < x) : 1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1) := by
  rw [div_sub_div _ _ hx.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg x]

lemma sum_inv_sq_range (M : ℕ) (hM : 0 < M) (d : ℕ) :
    ∑ i ∈ range d, 1 / ((M + 1 + i : ℕ) : ℝ) ^ 2 ≤ 1 / (M : ℝ) - 1 / ((M + d : ℕ) : ℝ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ]
    have hpos : (0 : ℝ) < ((M + d : ℕ) : ℝ) := by
      have : 0 < M + d := by omega
      exact_mod_cast this
    have h := inv_sq_succ_le ((M + d : ℕ) : ℝ) hpos
    have e1 : ((M + 1 + d : ℕ) : ℝ) = ((M + d : ℕ) : ℝ) + 1 := by push_cast; ring
    have e2 : ((M + (d + 1) : ℕ) : ℝ) = ((M + d : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [e1, e2]
    linarith

/-- The "tail" (off-lobe) frequencies: those at circular distance `> M` from `0`. -/
def tail (N M : ℕ) : Finset ℕ := (range N).filter (fun w => M < w ∧ w + M < N)

lemma sum_tail_inv_sq (N M : ℕ) (hM : 0 < M) :
    ∑ w ∈ tail N M, 1 / (w : ℝ) ^ 2 ≤ 1 / (M : ℝ) := by
  have hsub : tail N M ⊆ Ico (M + 1) N := by
    intro w hw
    simp only [tail, mem_filter, mem_range] at hw
    simp only [mem_Ico]
    omega
  calc ∑ w ∈ tail N M, 1 / (w : ℝ) ^ 2 ≤ ∑ w ∈ Ico (M + 1) N, 1 / (w : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ i ∈ range (N - (M + 1)), 1 / ((M + 1 + i : ℕ) : ℝ) ^ 2 := by
        rw [sum_Ico_eq_sum_range]
    _ ≤ 1 / (M : ℝ) - 1 / ((M + (N - (M + 1)) : ℕ) : ℝ) := sum_inv_sq_range M hM _
    _ ≤ 1 / (M : ℝ) := by
        have : (0 : ℝ) ≤ 1 / ((M + (N - (M + 1)) : ℕ) : ℝ) := by positivity
        linarith

lemma sum_tail_inv_sq_reflect (N M : ℕ) (hM : 0 < M) :
    ∑ w ∈ tail N M, 1 / ((N : ℝ) - w) ^ 2 ≤ 1 / (M : ℝ) := by
  have e : ∑ w ∈ tail N M, 1 / ((N : ℝ) - w) ^ 2 = ∑ w ∈ tail N M, 1 / (w : ℝ) ^ 2 := by
    refine sum_nbij' (fun w => N - w) (fun w => N - w) ?_ ?_ ?_ ?_ ?_
    · intro w hw
      simp only [tail, mem_filter, mem_range] at hw ⊢
      omega
    · intro w hw
      simp only [tail, mem_filter, mem_range] at hw ⊢
      omega
    · intro w hw
      simp only [tail, mem_filter, mem_range] at hw
      omega
    · intro w hw
      simp only [tail, mem_filter, mem_range] at hw
      omega
    · intro w hw
      simp only [tail, mem_filter, mem_range] at hw
      rw [Nat.cast_sub (by omega)]
  rw [e]
  exact sum_tail_inv_sq N M hM

/-- Tail mass of the squared Dirichlet kernel on the DFT grid. -/
lemma sum_tail_dir_sq (N a M : ℕ) (hM : 0 < M) :
    ∑ w ∈ tail N M, ‖dir N a w‖ ^ 2 ≤ (N : ℝ) ^ 2 / (2 * M) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  calc ∑ w ∈ tail N M, ‖dir N a w‖ ^ 2
      ≤ ∑ w ∈ tail N M, (N : ℝ) ^ 2 / 4 * (1 / (w : ℝ) ^ 2 + 1 / ((N : ℝ) - w) ^ 2) := by
        refine sum_le_sum fun w hw => ?_
        simp only [tail, mem_filter, mem_range] at hw
        exact dir_sq_le (by omega) (by omega)
    _ = (N : ℝ) ^ 2 / 4 *
          (∑ w ∈ tail N M, 1 / (w : ℝ) ^ 2 + ∑ w ∈ tail N M, 1 / ((N : ℝ) - w) ^ 2) := by
        rw [← mul_sum, sum_add_distrib]
    _ ≤ (N : ℝ) ^ 2 / 4 * (1 / (M : ℝ) + 1 / (M : ℝ)) := by
        gcongr
        · exact sum_tail_inv_sq N M hM
        · exact sum_tail_inv_sq_reflect N M hM
    _ = (N : ℝ) ^ 2 / (2 * M) := by
        field_simp
        ring

/-- The main lobe has at most `2 M + 1` grid points. -/
lemma card_lobe_le (N M : ℕ) :
    ((range N).filter (fun w => ¬ (M < w ∧ w + M < N))).card ≤ 2 * M + 1 := by
  have hsub : (range N).filter (fun w => ¬ (M < w ∧ w + M < N))
      ⊆ range (M + 1) ∪ Ico (N - M) N := by
    intro w hw
    simp only [mem_filter, mem_range] at hw
    simp only [mem_union, mem_range, mem_Ico]
    omega
  calc _ ≤ (range (M + 1) ∪ Ico (N - M) N).card := card_le_card hsub
    _ ≤ (range (M + 1)).card + (Ico (N - M) N).card := card_union_le _ _
    _ ≤ 2 * M + 1 := by
        rw [card_range, Nat.card_Ico]
        omega

end FourierTreeRIP
