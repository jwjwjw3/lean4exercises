import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace C03S04

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  -- · apply h₀
  intro h
  apply h₁
  rw [h]
  -- linarith

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  ⟨h₀, h⟩

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  -- apply h.right
  apply h.2
  -- exact le_antisymm h.left h'
  exact le_antisymm h.1 h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  have ⟨h₀, h₁⟩ := h
  constructor
  · show m ∣ n
    apply h₀
  · show ¬n ∣ m
    contrapose! h₁
    apply dvd_antisymm h₀ h₁

example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5 / 2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  -- fun ⟨z, xltz, zlty⟩ ↦ lt_trans xltz zlty
  fun ⟨_, xltz, zlty⟩ ↦ lt_trans xltz zlty

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num

example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
    -- intro h'
    -- linarith
  contrapose!
  exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · show x ≤ y ∧ ¬y ≤ x → x ≤ y ∧ x ≠ y
    intro h
    have ⟨h₁, h₂⟩ := h
    constructor
    · apply h₁
    · contrapose! h₂
      linarith
  · show x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x
    intro h'
    have ⟨h₁', h₂'⟩ := h'
    constructor
    · apply h₁'
    · contrapose! h₂'
      linarith

theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by
    have h₁' : x ^ 2 ≥ 0 := by apply pow_two_nonneg
    have h₂' : y ^ 2 ≥ 0 := by apply pow_two_nonneg
    linarith
    -- contrapose! h₂'
    -- apply add_eq_zero_iff_neg_eq.mp at h
    -- have h₃' : x ^ 2 > 0 := by
    --   apply lt_of_le_of_ne' h₁'
    --   apply h₂'
    -- apply neg_lt_zero.mpr at h₃'
    -- rw [h] at h₃'
    -- exact h₃'
  -- have h' : x ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
  pow_eq_zero h'


example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · show x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0
    intro h
    constructor
    · apply aux h
    · rw [add_comm] at h
      apply aux h
  · show x = 0 ∧ y = 0 → x ^ 2 + y ^ 2 = 0
    intro h'
    have ⟨h₁', h₂'⟩ := h'
    rw [h₁', h₂']
    norm_num

section

example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num

end

theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl

example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [Monotone]
  push_neg
  use 1
  use 2
  norm_num

section
variable {α : Type*} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_le]
  constructor
  · show a ≤ b ∧ ¬b ≤ a → a ≤ b ∧ a ≠ b
    rintro ⟨h₁, h₂⟩
    constructor
    · assumption
    · contrapose! h₂
      rw [h₂]
  · show a ≤ b ∧ a ≠ b → a ≤ b ∧ ¬b ≤ a
    rintro ⟨h₁', h₂'⟩
    constructor
    · assumption
    · contrapose! h₂'
      apply le_antisymm h₁' h₂'

end

section
variable {α : Type*} [Preorder α]
variable (a b c : α)

example : ¬a < a := by
  rw [lt_iff_le_not_le]
  by_contra h
  have ⟨h₁, h₂⟩ := h
  apply h₂ at h₁
  exact h₁

example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_le]
  rintro ⟨h₁, _⟩
  rintro ⟨h₃, h₄⟩
  constructor
  · show a ≤ c
    apply le_trans h₁ h₃
  · show ¬c ≤ a
    contrapose! h₄
    apply le_trans h₄ h₁

end
