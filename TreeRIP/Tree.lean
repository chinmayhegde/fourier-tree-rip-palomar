module

public import TreeRIP.Defs

@[expose] public section

/-! # The broom ("stem plus bush") tree -/

namespace FourierTreeRIP

open Finset

/-- The broom at stem node `n`: the top `2^r` nodes of relative level `r + 1` below `n`,
the complete subtree below `n` through relative depth `r`, and the path from the root
to `n`. -/
def broom (r h n : ℕ) : Finset ℕ :=
  (Ico (2 * (2 ^ r * n)) (2 * (2 ^ r * n) + 2 ^ r)
    ∪ (range (r + 1)).biUnion (fun i => Ico (2 ^ i * n) (2 ^ i * n + 2 ^ i)))
    ∪ ((range (h + 1)).image (fun t => n / 2 ^ t)).filter (fun j => 1 ≤ j)

lemma mem_broom {r h n j : ℕ} : j ∈ broom r h n ↔
    ((2 * (2 ^ r * n) ≤ j ∧ j < 2 * (2 ^ r * n) + 2 ^ r)
      ∨ ∃ i, i < r + 1 ∧ 2 ^ i * n ≤ j ∧ j < 2 ^ i * n + 2 ^ i)
      ∨ ((∃ t, t < h + 1 ∧ n / 2 ^ t = j) ∧ 1 ≤ j) := by
  simp only [broom, mem_union, mem_Ico, mem_biUnion, mem_range, mem_filter, mem_image]

lemma broom_isRootedSubtree {r h n : ℕ} (hn : 1 ≤ n) (hnh : n ≤ 2 ^ h) :
    IsRootedSubtree (broom r h n) := by
  intro j hj
  rw [mem_broom] at hj
  rcases hj with (⟨h1, h2⟩ | ⟨i, hi, h1, h2⟩) | ⟨⟨t, ht, rfl⟩, h1⟩
  · have hb : 1 ≤ 2 ^ r * n := Nat.mul_pos (by positivity) hn
    refine ⟨by omega, fun _ => ?_⟩
    rw [mem_broom]
    left; right
    exact ⟨r, by omega, by omega, by omega⟩
  · have hb : 1 ≤ 2 ^ i * n := Nat.mul_pos (by positivity) hn
    refine ⟨by omega, fun hj2 => ?_⟩
    rw [mem_broom]
    rcases i with _ | i
    · -- `j = n`
      simp only [pow_zero, one_mul] at h1 h2
      have hjn : j = n := by omega
      right
      have hh : 1 ≤ h := by
        rcases h with _ | h
        · simp at hnh; omega
        · omega
      refine ⟨⟨1, by omega, by rw [hjn]; simp⟩, by omega⟩
    · left; right
      have e : 2 ^ (i + 1) = 2 * 2 ^ i := by ring
      rw [e] at h1 h2
      have e' : 2 * 2 ^ i * n = 2 * (2 ^ i * n) := by ring
      rw [e'] at h1 h2
      exact ⟨i, by omega, by omega, by omega⟩
  · refine ⟨h1, fun hj2 => ?_⟩
    rw [mem_broom]
    right
    have hdd : n / 2 ^ t / 2 = n / 2 ^ (t + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ]
    have ht1 : t + 1 < h + 1 := by
      by_contra hcon
      have hht : h ≤ t := by omega
      have : n < 2 * 2 ^ t := by
        calc n ≤ 2 ^ h := hnh
          _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) hht
          _ < 2 * 2 ^ t := by
              have : 0 < 2 ^ t := by positivity
              omega
      have : n / 2 ^ t < 2 := by
        rw [Nat.div_lt_iff_lt_mul (by positivity)]
        omega
      omega
    exact ⟨⟨t + 1, ht1, hdd.symm⟩, by omega⟩

lemma sum_two_pow (n : ℕ) : ∑ i ∈ range n, 2 ^ i + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, pow_succ]; omega

lemma broom_card_le (r h n : ℕ) : (broom r h n).card ≤ h + 3 * 2 ^ r := by
  unfold broom
  have h1 : (Ico (2 * (2 ^ r * n)) (2 * (2 ^ r * n) + 2 ^ r)).card = 2 ^ r := by
    rw [Nat.card_Ico, Nat.add_sub_cancel_left]
  have h2 : ((range (r + 1)).biUnion (fun i => Ico (2 ^ i * n) (2 ^ i * n + 2 ^ i))).card
      ≤ ∑ i ∈ range (r + 1), 2 ^ i := by
    refine le_trans card_biUnion_le (le_of_eq ?_)
    refine sum_congr rfl fun i _ => ?_
    rw [Nat.card_Ico, Nat.add_sub_cancel_left]
  have h3 : (((range (h + 1)).image (fun t => n / 2 ^ t)).filter (fun j => 1 ≤ j)).card
      ≤ h + 1 := by
    refine le_trans (card_filter_le _ _) (le_trans card_image_le ?_)
    rw [card_range]
  have h4 := sum_two_pow (r + 1)
  have e : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
  have c1 := card_union_le
    (Ico (2 * (2 ^ r * n)) (2 * (2 ^ r * n) + 2 ^ r)
      ∪ (range (r + 1)).biUnion (fun i => Ico (2 ^ i * n) (2 ^ i * n + 2 ^ i)))
    (((range (h + 1)).image (fun t => n / 2 ^ t)).filter (fun j => 1 ≤ j))
  have c2 := card_union_le
    (Ico (2 * (2 ^ r * n)) (2 * (2 ^ r * n) + 2 ^ r))
    ((range (r + 1)).biUnion (fun i => Ico (2 ^ i * n) (2 ^ i * n + 2 ^ i)))
  omega

lemma lower_mem_broom {r h n j : ℕ} (h1 : 2 ^ r * n ≤ j) (h2 : j < 2 ^ r * n + 2 ^ r) :
    j ∈ broom r h n := by
  rw [mem_broom]
  left; right
  exact ⟨r, by omega, h1, h2⟩

lemma upper_mem_broom {r h n j : ℕ} (h1 : 2 * (2 ^ r * n) ≤ j)
    (h2 : j < 2 * (2 ^ r * n) + 2 ^ r) : j ∈ broom r h n := by
  rw [mem_broom]
  left; left
  exact ⟨h1, h2⟩

end FourierTreeRIP
