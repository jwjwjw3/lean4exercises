import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

#check le_max_left

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  · show max a b ≤ max b a
    apply max_le
    apply le_max_right
    apply le_max_left
  · show max b a ≤ max a b
    apply max_le
    apply le_max_right
    apply le_max_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · show min (min a b) c ≤ min a (min b c)
    apply le_min
    · show min (min a b) c ≤ a
      apply le_trans
      apply min_le_left (min a b) c
      apply min_le_left
    · show min (min a b) c ≤ min b c
      apply le_min
      · show min (min a b) c ≤ b
        apply le_trans
        apply min_le_left (min a b) c
        apply min_le_right
      · show min (min a b) c ≤ c
        apply min_le_right
  · show min a (min b c) ≤ min (min a b) c
    apply le_min
    · show min a (min b c) ≤ min a b
      apply le_min
      · show min a (min b c) ≤ a
        apply min_le_left
      · show min a (min b c) ≤ b
        apply le_trans
        apply min_le_right
        apply min_le_left
    · show min a (min b c) ≤ c
      apply le_trans
      apply min_le_right
      apply min_le_right

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · show min a b + c ≤ a + c
    apply add_le_add_right
    apply min_le_left
  · show min a b + c ≤ b + c
    apply add_le_add_right
    apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · show min a b + c ≤ min (a + c) (b + c)
    apply aux
  · show min (a + c) (b + c) ≤ min a b + c
    nth_rewrite 2 [<-add_neg_cancel_right a c]
    nth_rewrite 2 [<-add_neg_cancel_right b c]
    rw [<-add_neg_cancel_right (min (a + c) (b + c)) c]
    rw [add_assoc]
    nth_rewrite 4 [add_comm]
    rw [<-add_assoc]
    apply add_le_add_right
    apply aux

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have h: |a| ≤ |a-b| + |b| := by
    nth_rewrite 1 [<-sub_add_cancel a b]
    apply abs_add
  apply sub_le_iff_le_add.mpr at h
  exact h
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · show x ∣ y * (x * z) + x ^ 2
    apply dvd_add
    · show x ∣ y * (x * z)
      rw [<-mul_assoc, mul_comm, <-mul_assoc]
      apply dvd_mul_left
    · show x ∣ x ^ 2
      apply dvd_mul_left
  · show x ∣ w ^ 2
    apply dvd_trans
    apply h
    apply dvd_mul_left

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  · show m.gcd n ∣ n.gcd m
    apply Nat.dvd_gcd
    · show m.gcd n ∣ n
      apply Nat.gcd_dvd_right
    · show m.gcd n ∣ m
      apply Nat.gcd_dvd_left
  · show n.gcd m ∣ m.gcd n
    apply Nat.dvd_gcd
    · show n.gcd m ∣ m
      apply Nat.gcd_dvd_right
    · show n.gcd m ∣ n
      apply Nat.gcd_dvd_left
end
