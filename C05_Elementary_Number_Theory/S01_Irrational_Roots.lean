import MIL.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic

-- #print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

-- #check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p
  -- rw [Nat.prime_def_lt] at prime_p
  -- exact prime_p


-- #check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

-- #check Nat.Prime.dvd_mul
-- #check Nat.prime_two
-- #check Nat.Prime.dvd_mul Nat.prime_two
-- #check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have h₁: 2 ∣ m := by
    apply even_of_even_sqr; use n ^ 2
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp h₁
  have h₂: 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]; ring
  have h₃: 2 * k ^ 2 = n ^ 2 := by
    norm_num at h₂; exact h₂
  have h₄: 2 ∣ n := by
    apply even_of_even_sqr; use k ^ 2; symm; exact h₃
  have h₅: 2 ∣ m.gcd n := by
    apply Nat.dvd_gcd; apply h₁; apply h₄
  have : 2 ∣ 1 := by
    rw [coprime_mn] at h₅; exact h₅
  norm_num at this


theorem prime_of_prime_sqr {m p: ℕ} (prime_p: Nat.Prime p) (h : p ∣ m ^ 2) : p ∣ m := by
  rw [pow_two, Nat.Prime.dvd_mul] at h
  cases h <;> assumption; exact prime_p

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have h₀: 1 < p := by calc
    1 < 2 := by norm_num
    _ ≤ p := by exact Nat.Prime.two_le prime_p
  have h₁: p ∣ m := by
    apply prime_of_prime_sqr; apply prime_p; use n ^ 2
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp h₁
  have h₂: p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq, meq]; ring
  have h₃: p * k ^ 2 = n ^ 2 := by
    have h₂' : p ≠ 0 := by exact prime_p.ne_zero
    apply (mul_right_inj' h₂').mp at h₂
    exact h₂
  have h₄: p ∣ n := by
    apply prime_of_prime_sqr; apply prime_p; use k ^ 2; symm; exact h₃
  have h₅: p ∣ m.gcd n := by
    apply Nat.dvd_gcd; apply h₁; apply h₄
  have h₆: p ∣ 1 := by
    rw [coprime_mn] at h₅; exact h₅
  have h₆'': p ≠ 1 := by exact Ne.symm (Nat.ne_of_lt h₀)
  norm_num at h₆
  apply h₆'' at h₆
  exact h₆

-- #check Nat.primeFactorsList
-- #check Nat.prime_of_mem_primeFactorsList
-- #check Nat.prod_primeFactorsList
-- #check Nat.primeFactorsList_unique

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    rw [factorization_pow']
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    rw [factorization_mul' prime_p.ne_zero nsqr_nez]
    rw [factorization_pow']
    rw [Nat.Prime.factorization' prime_p]
    ring
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this


example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    rw [factorization_pow']
  have eq2 : ((r + 1) * n ^ k).factorization p =
      k * n.factorization p + (r + 1).factorization p := by
    rw [factorization_mul', factorization_pow']
    ring
    norm_num
    apply npow_nz
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  rw [← Nat.mul_sub]
  exact Nat.dvd_mul_right k (m.factorization p - n.factorization p)

-- #check multiplicity
