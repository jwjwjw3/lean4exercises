import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h
  -- have h': 0 ≤ y ∨ y < 0 := by
  --   apply le_or_gt 0 y
  -- rcases h' with h₀ | h₁
  -- · rw [abs_of_nonneg h₀]
  --   intro h; left; exact h
  -- · rw [abs_of_neg h₁]
  --   intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h₁ | h₂
  · rw [abs_of_nonneg h₁]
  · rw [abs_of_neg h₂]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h₁ | h₂
  · rw [abs_of_nonneg h₁]
    linarith
  · rw [abs_of_neg h₂]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x+y) with sp | sn
  · rw [abs_of_nonneg sp]
    linarith [le_abs_self x, le_abs_self y]
  · rw [abs_of_neg sn]
    linarith [neg_le_abs_self x, neg_le_abs_self y]


theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · show x < |y| → x < y ∨ x < -y
    rcases le_or_gt 0 y with hp | hn
    · rw [abs_of_nonneg hp]
      intro h; left; exact h
    · rw [abs_of_neg hn]
      intro h; right; exact h
  · show x < y ∨ x < -y → x < |y|
    rcases le_or_gt 0 y with hp | hn
    · rw [abs_of_nonneg hp]
      intro h
      rcases h with h₁ | h₂
      · apply h₁
      · linarith
    · rw [abs_of_neg hn]
      intro h
      rcases h with h₁ | h₂
      · linarith
      · exact h₂
      -- contrapose! h
      -- constructor
      -- · linarith
      -- · exact h

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · show |x| < y → -y < x ∧ x < y
    intro h
    rcases le_or_gt 0 x with hp | hn
    · rw [abs_of_nonneg hp] at h
      constructor
      · linarith
      · exact h
    · rw [abs_of_neg hn] at h
      constructor
      · linarith
      · linarith
  · show -y < x ∧ x < y → |x| < y
    intro h
    rcases le_or_gt 0 x with hp | hn
    · rw [abs_of_nonneg hp]
      exact h.right
    · rw [abs_of_neg hn]
      linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, h₁ | h₂⟩ <;> linarith [pow_two_nonneg x, pow_two_nonneg y]
  -- rcases h with ⟨x, y, h₁ | h₂⟩
  -- · linarith [pow_two_nonneg x, pow_two_nonneg y]
  -- · linarith [pow_two_nonneg x, pow_two_nonneg y]
  -- contrapose! h
  -- intro x y
  -- have h: x^2 + y^2 ≥ 0 := by
  --   have h' : x^2 ≥ 0 := by apply pow_two_nonneg
  --   have h'' : y^2 ≥ 0 := by apply pow_two_nonneg
  --   linarith
  -- constructor
  -- · linarith
  -- · linarith


example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : (x-1) * (x+1) = 0 := by linarith
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h'
  rcases h' with h₁' | h₂'
  · left
    linarith
  · right
    linarith


example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : (x-y) * (x+y) = 0 := by linarith
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h'
  rcases h' with h₁' | h₂'
  · left
    linarith
  · right
    linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : (x-1) * (x+1) = 0 := by
    ring_nf
    rw [h]
    ring
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h'
  rcases h' with h₁' | h₂'
  · left
    apply eq_of_sub_eq_zero
    exact h₁'
  · right
    apply eq_neg_iff_add_eq_zero.mpr
    exact h₂'

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · show (P → Q) → ¬P ∨ Q
    intro h
    by_cases h': P
    · apply h at h'
      right
      exact h'
    · left
      exact h'
  · show ¬P ∨ Q → P → Q
    intro h
    contrapose! h
    exact h
