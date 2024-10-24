import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  -- ring_nf
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  -- have h' : 1 * a < a * a := by
  --   have h'': 0 < a := by linarith
  --   apply (mul_lt_mul_right h'').mpr
  --   apply h
  -- linarith
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n _
  simp
  -- rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro k hk
  have kdef : max Ns Nt ≤ k := by linarith
  have Nslek: Ns ≤ k := by apply max_le_iff.mp at kdef; exact kdef.1
  have Ntlek: Nt ≤ k := by apply max_le_iff.mp at kdef; exact kdef.2
  calc
    |s k + t k - (a + b)| = |(s k - a) + (t k - b)| := by ring_nf
    _ ≤ |(s k - a)| + |(t k - b)| := by apply abs_add_le
    _ < ε / 2  + ε / 2 := by apply add_lt_add; apply hs; apply Nslek; apply ht; apply Ntlek
    _ = ε := by norm_num

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε eppos
  dsimp
  have ep_dv_abs_c_pos: 0 < ε / |c| := by apply div_pos eppos acpos
  rcases cs (ε/|c|) ep_dv_abs_c_pos with ⟨Nx, h'⟩
  use Nx
  intro k hk
  calc
    |c * s k - c * a| = |c * (s k - a)| := by ring_nf
    _ = |c| * |s k - a| := by rw [abs_mul]
    _ < |c| * (ε / |c|) := by apply mul_lt_mul_of_pos_left; apply h'; apply hk; apply acpos
    _ = |c| / |c| * ε := by ring
    _ = 1 * ε := by rw [div_self]; linarith
    _ = ε := by norm_num

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro k hk
  have h' : |s k| - |a| < 1 := by
    calc
      |s k| - |a| ≤ |s k - a| := by apply abs_sub_abs_le_abs_sub
      _ < 1 := by apply h; apply hk
  linarith

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₁ N₀
  intro n Nn
  have N0_le_n : N₀ ≤ n := by exact le_of_max_le_right Nn
  have N1_le_n : N₁ ≤ n := by exact le_of_max_le_left Nn
  calc
    |s n * t n - 0| = |s n * (t n -0)| := by norm_num
    _ = |s n| * |t n - 0| := by apply abs_mul
    _ < B * (ε / B) := by
      apply mul_lt_mul_of_nonneg
      apply h₀; apply N0_le_n
      apply h₁; apply N1_le_n
      apply abs_nonneg; apply abs_nonneg
    _ = B / B * ε := by ring_nf
    _ = 1 * ε := by rw [div_self]; linarith
    _ = ε := by norm_num

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have h₂:= convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert h₂ using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have h : |a - b| > 0 := by exact abs_sub_pos.mpr abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
    -- calc
    --   ε = |a - b| / 2 := by rfl
    --   _ > 0 := by linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by apply hNa; apply le_max_left
  have absb : |s N - b| < ε := by apply hNb; apply le_max_right
  have : |a - b| < |a - b| := by
    calc
      |a - b| = |(s N - b) - (s N - a)| := by ring_nf
      _ ≤ |s N - b| + |s N - a| := by exact abs_sub (s N - b) (s N - a)
      _ < ε + ε := by apply add_lt_add absb absa
      _ = 2 * ε := by ring
      _ = |a - b| := by
          change 2 * (|a-b|/2) = |a - b|
          linarith
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
