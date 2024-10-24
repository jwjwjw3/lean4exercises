import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  · show x ⊓ y ≤ y ⊓ x
    apply le_inf
    apply inf_le_right
    apply inf_le_left
  · show y ⊓ x ≤ x ⊓ y
    apply le_inf
    apply inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · show x ⊓ y ⊓ z ≤ x ⊓ (y ⊓ z)
    apply le_inf
    · show x ⊓ y ⊓ z ≤ x
      trans x ⊓ y
      apply inf_le_left
      apply inf_le_left
    · show x ⊓ y ⊓ z ≤ y ⊓ z
      apply le_inf
      · show x ⊓ y ⊓ z ≤ y
        trans x ⊓ y
        apply inf_le_left
        apply inf_le_right
      · show x ⊓ y ⊓ z ≤ z
        apply inf_le_right
  · show x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z
    apply le_inf
    · show x ⊓ (y ⊓ z) ≤ x ⊓ y
      apply le_inf
      · show x ⊓ (y ⊓ z) ≤ x
        apply inf_le_left
      · show x ⊓ (y ⊓ z) ≤ y
        trans y ⊓ z
        apply inf_le_right
        apply inf_le_left
    · show x ⊓ (y ⊓ z) ≤ z
      trans y ⊓ z
      apply inf_le_right
      apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · show x ⊔ y ≤ y ⊔ x
    apply sup_le
    apply le_sup_right
    apply le_sup_left
  · show y ⊔ x ≤ x ⊔ y
    apply sup_le
    apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · show x ⊔ y ⊔ z ≤ x ⊔ (y ⊔ z)
    apply sup_le
    · show x ⊔ y ≤ x ⊔ (y ⊔ z)
      apply sup_le
      · show x ≤ x ⊔ (y ⊔ z)
        apply le_sup_left
      · show y ≤ x ⊔ (y ⊔ z)
        trans y ⊔ z
        apply le_sup_left
        apply le_sup_right
    · show z ≤ x ⊔ (y ⊔ z)
      trans y ⊔ z
      apply le_sup_right
      apply le_sup_right
  · show x ⊔ (y ⊔ z) ≤ x ⊔ y ⊔ z
    apply sup_le
    · show x ≤ x ⊔ y ⊔ z
      trans x ⊔ y
      apply le_sup_left
      apply le_sup_left
    · show y ⊔ z ≤ x ⊔ y ⊔ z
      apply sup_le
      · show y ≤ x ⊔ y ⊔ z
        trans x ⊔ y
        apply le_sup_right
        apply le_sup_left
      · show z ≤ x ⊔ y ⊔ z
        apply le_sup_right

--   apply le_antisymm
--   · apply sup_le
--     · apply sup_le
--       · apply le_sup_left
--       · trans y ⊔ z
--         apply le_sup_left
--         apply le_sup_right
--     · trans y ⊔ z
--       apply le_sup_right
--       apply le_sup_right
--   · apply sup_le
--     · trans x ⊔ y
--       apply le_sup_left
--       apply le_sup_left
--     · apply sup_le
--       · trans x ⊔ y
--         apply le_sup_right
--         apply le_sup_left
--       · apply le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · show x ⊓ (x ⊔ y) ≤ x
    apply inf_le_left
  · show x ≤ x ⊓ (x ⊔ y)
    apply le_inf
    · show x ≤ x
      apply le_refl
    · show x ≤ x ⊔ y
      apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · show x ⊔ (x ⊓ y) ≤ x
    apply sup_le
    · show x ≤ x
      apply le_refl
    · show x ⊓ y ≤ x
      apply inf_le_left
  · show x ≤ x ⊔ (x ⊓ y)
    apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, @inf_comm _ _ (a ⊔ b), absorb1, @inf_comm _ _ (a ⊔ b), h, ← sup_assoc, @inf_comm _ _ c a,
    absorb2, inf_comm]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h]
  nth_rewrite 2 [sup_comm]
  rw [absorb2]
  nth_rewrite 2 [sup_comm]
  rw [h]
  rw [<-inf_assoc]
  nth_rewrite 2 [sup_comm]
  rw [absorb1]
  nth_rewrite 2 [sup_comm]
  rfl

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check sub_le_sub_right

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

theorem aux1 (h : a ≤ b) : 0 ≤ b - a := by
  rw [<-sub_self a]
  apply sub_le_sub_right
  apply h

theorem aux2 (h: 0 ≤ b - a) : a ≤ b := by
  rw [<-sub_self a] at h
  have h1 : a - a + a ≤ b - a + a := by
    apply add_le_add_right
    apply h
  repeat rw [sub_add_cancel] at h1
  exact h1


theorem aux3 (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  apply aux1 at h
  apply aux2
  rw [<-sub_mul]
  apply mul_nonneg h h'

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h: dist x x ≤ dist x y + dist y x := by
    apply dist_triangle x y x
  nth_rewrite 3 [dist_comm] at h
  rw [dist_self] at h
  linarith

end
