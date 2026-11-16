module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.Fintype.Pigeonhole

public section

/-! # Simultaneous Dirichlet approximation (circle form, `Q = 16`) -/

namespace FourierTreeRIP

open Complex in
/-- For finitely many reals `α i` there is `1 ≤ n ≤ 16 ^ #ι` such that every
`exp (2 π i α_i n)` is within `1/2` of `1`. -/
theorem exists_simultaneous_approx {ι : Type*} [Fintype ι] (α : ι → ℝ) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 16 ^ Fintype.card ι ∧
      ∀ i, ‖Complex.exp (2 * Real.pi * Complex.I * (α i : ℂ) * (n : ℂ)) - 1‖ ≤ 1 / 2 := by
  classical
  have hfr : ∀ (n : ℕ) (i : ι), ⌊16 * Int.fract ((n : ℝ) * α i)⌋₊ < 16 := by
    intro n i
    have h0 := Int.fract_nonneg ((n : ℝ) * α i)
    have h1 := Int.fract_lt_one ((n : ℝ) * α i)
    rw [Nat.floor_lt (by positivity)]
    push_cast; linarith
  let f : Fin (16 ^ Fintype.card ι + 1) → (ι → Fin 16) := fun n i =>
    ⟨⌊16 * Int.fract (((n : ℕ) : ℝ) * α i)⌋₊, hfr n i⟩
  have hcard : Fintype.card (ι → Fin 16) < Fintype.card (Fin (16 ^ Fintype.card ι + 1)) := by
    simp
  obtain ⟨n₁, n₂, hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  wlog hlt : (n₁ : ℕ) < n₂ generalizing n₁ n₂
  · have hne' : (n₁ : ℕ) ≠ n₂ := fun h => hne (Fin.ext h)
    exact this n₂ n₁ hne.symm hf.symm (by omega)
  refine ⟨n₂ - n₁, by omega, by have := n₂.2; omega, fun i => ?_⟩
  have hi : ⌊16 * Int.fract (((n₁ : ℕ) : ℝ) * α i)⌋₊ = ⌊16 * Int.fract (((n₂ : ℕ) : ℝ) * α i)⌋₊ := by
    have := congrFun hf i
    simpa [f] using congrArg Fin.val this
  have e1 : ((n₁ : ℕ) : ℝ) * α i = ⌊((n₁ : ℕ) : ℝ) * α i⌋ + Int.fract (((n₁ : ℕ) : ℝ) * α i) :=
    (Int.floor_add_fract _).symm
  have e2 : ((n₂ : ℕ) : ℝ) * α i = ⌊((n₂ : ℕ) : ℝ) * α i⌋ + Int.fract (((n₂ : ℕ) : ℝ) * α i) :=
    (Int.floor_add_fract _).symm
  have p1 := Int.fract_nonneg (((n₁ : ℕ) : ℝ) * α i)
  have p2 := Int.fract_nonneg (((n₂ : ℕ) : ℝ) * α i)
  generalize Int.fract (((n₁ : ℕ) : ℝ) * α i) = x₁ at hi e1 p1
  generalize Int.fract (((n₂ : ℕ) : ℝ) * α i) = x₂ at hi e2 p2
  generalize ⌊((n₁ : ℕ) : ℝ) * α i⌋ = k₁ at e1
  generalize ⌊((n₂ : ℕ) : ℝ) * α i⌋ = k₂ at e2
  have hd : |x₂ - x₁| ≤ 1 / 16 := by
    have a1 := Nat.floor_le (show (0 : ℝ) ≤ 16 * x₁ by positivity)
    have a2 := Nat.lt_floor_add_one (16 * x₁)
    have b1 := Nat.floor_le (show (0 : ℝ) ≤ 16 * x₂ by positivity)
    have b2 := Nat.lt_floor_add_one (16 * x₂)
    rw [hi] at a1 a2
    rw [abs_le]; constructor <;> linarith
  have key : Complex.exp (2 * Real.pi * Complex.I * (α i : ℂ) * (((n₂ : ℕ) - (n₁ : ℕ) : ℕ) : ℂ))
      = Complex.exp (Complex.I * ((2 * Real.pi * (x₂ - x₁) : ℝ) : ℂ)) := by
    have e1c := congrArg (fun t : ℝ => (t : ℂ)) e1
    have e2c := congrArg (fun t : ℝ => (t : ℂ)) e2
    simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_intCast] at e1c e2c
    have : 2 * Real.pi * Complex.I * (α i : ℂ) * (((n₂ : ℕ) - (n₁ : ℕ) : ℕ) : ℂ)
        = Complex.I * ((2 * Real.pi * (x₂ - x₁) : ℝ) : ℂ)
          + ((k₂ - k₁ : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [Nat.cast_sub hlt.le]
      push_cast
      linear_combination (2 * Real.pi * Complex.I) * e2c - (2 * Real.pi * Complex.I) * e1c
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [key]
  calc ‖Complex.exp (Complex.I * ((2 * Real.pi * (x₂ - x₁) : ℝ) : ℂ)) - 1‖
      ≤ ‖2 * Real.pi * (x₂ - x₁)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |x₂ - x₁| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
    _ ≤ 2 * 4 * (1 / 16) := by
        gcongr
        exact Real.pi_le_four
    _ = 1 / 2 := by norm_num

end FourierTreeRIP
