import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common


section matrices

-- Adding vectors
-- #eval !![1, 2] + !![3, 4]  -- !![4, 6]

-- Adding matrices
-- #eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]

-- Multiplying matrices
-- #eval !![1, 2; 3, 4] * !![3, 4; 5, 6]  -- !![4, 6; 8, 10]

-- #check Matrix

open Matrix

-- matrices acting on vectors on the left
-- #eval !![1, 2; 3, 4] *ᵥ ![1, 1] -- ![3, 7]

-- matrices acting on vectors on the left, resulting in a size one matrix
-- #eval !![1, 2] *ᵥ ![1, 1]  -- ![3]

-- #eval ![1, 2] *ᵥ ![1, 1]  -- ![2, 4] -- not-common
-- #eval ![1, 2] * ![1, 1]  -- ![1, 2]
-- #eval ![1, 2] * ![1, 5]  -- ![1, 10]

-- matrices acting on vectors on the right
-- #eval  ![1, 1, 1] ᵥ* !![1, 2; 3, 4; 5, 6] -- ![9, 12]

-- Note that these two below gives different results
-- #eval ![2, 3] *ᵥ !![1, 2; 3, 4]  -- not-common
-- #eval ![2, 3] ᵥ* !![1, 2; 3, 4]
-- #eval ![2, 3] * !![1, 2; 3, 4]  -- this gives synthesize error

-- #eval row (Fin 1) ![1, 2] -- !![1, 2]
-- #eval col (Fin 1) ![1, 2] -- !![1; 2]

-- #eval row (Fin 2) ![1, 2] -- !![1, 2]
-- #eval col (Fin 2) ![1, 2] -- !![1; 2]

-- vector dot product
-- #eval ![1, 2] ⬝ᵥ ![3, 4] -- `11`

-- matrix transpose
-- #eval !![1, 2; 3, 4]ᵀ -- `!![1, 3; 2, 4]`

-- determinant
-- #eval !![(1 : ℤ), 2; 3, 4].det -- `-2`

-- trace
-- #eval !![(1 : ℤ), 2; 3, 4].trace -- `5`

-- #eval !![(1 : ℝ), 2; 3, 4].trace -- `5` -- gives silent failure of Real.ofCauchy (sorry...) since ℝ is non-computable, cannot use #eval


-- Note that ℝ is non-computable
-- #simp !![(1 : ℝ), 2; 3, 4].det -- `4 - 2*3`

-- #norm_num !![(1 : ℝ), 2; 3, 4].det -- `-2`

-- #norm_num !![(1 : ℝ), 2; 3, 4].trace -- `5`

variable (a b c d : ℝ) in

-- #simp !![a, b; c, d].det -- `a * d – b * c`

-- #norm_num [Matrix.inv_def] !![(1 : ℝ), 2; 3, 4]⁻¹ -- !![-2, 1; 3 / 2, -(1 / 2)]


-- Special case: like division of numbers returns the artificial value zero for division by zero, inversion is defined on all matrices and returns the zero matrix for non-invertible matrices, as below:
-- #eval 1 / 0
-- #norm_num [Matrix.inv_def] !![(1 : ℝ), 2; 1, 2]⁻¹ -- !![-2, 1; 3 / 2, -(1 / 2)]

-- #check IsUnit

example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
  have : Invertible !![(1 : ℝ), 2; 3, 4] := by
    apply Matrix.invertibleOfIsUnitDet
    -- simp
    norm_num
  simp

example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
  rw [Matrix.inv_def]
  simp
  ring_nf
  apply Eq.symm one_fin_two
  -- norm_num [Matrix.inv_def]
  -- exact one_fin_two.symm

section

example : (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![1, 1; 1, 1] := by
  ext i j
  fin_cases i
  · fin_cases j
    · rfl
    · rfl
  · fin_cases j
    · rfl
    · rfl
  -- fin_cases i <;> fin_cases j <;> rfl

example : (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) * (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![1, 1; 1, 1] := by
  ext i j
  -- fin_cases i <;> fin_cases j <;> rfl
  fin_cases i <;> fin_cases j <;> norm_num

example : !![1, 1; 1, 1] * !![1, 1; 1, 1] = !![2, 2; 2, 2] := by
  norm_num

example : Matrix.of (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) * Matrix.of (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![2, 2; 2, 2] := by
  have h: Matrix.of (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![1, 1; 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  repeat rw [h]
  norm_num

example {n : ℕ} (v : Fin n → ℝ) :
    Matrix.vandermonde v = Matrix.of (fun i j : Fin n ↦ v i ^ (j : ℕ)) :=
  rfl

-- #eval !![1, 2; 3, 4] 1 1

example : !![1, 2; 3, 4] 1 1 = 4 := by
  simp

end

end matrices


variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section

variable {ι : Type*} (B : Basis ι K V) (v : V) (i : ι)

-- The basis vector with index ``i``
-- #check (B i : V)

-- the linear isomorphism with the model space given by ``B``, using →₀ for finite support
-- #check (B.repr : V ≃ₗ[K] ι →₀ K)

-- the component function of ``v``
-- #check (B.repr v : ι →₀ K)

-- the component of ``v`` with index ``i``
-- #check (B.repr v i : K)

noncomputable example (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) : Basis ι K V :=
  Basis.mk b_indep (fun v _ ↦ b_spans v)

-- The family of vectors underlying the above basis is indeed ``b``.
example (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) (i : ι) :
    Basis.mk b_indep (fun v _ ↦ b_spans v) i = b i :=
  Basis.mk_apply b_indep (fun v _ ↦ b_spans v) i

variable [DecidableEq ι]

example : Finsupp.basisSingleOne.repr = LinearEquiv.refl K (ι →₀ K) :=
  rfl

-- #check Finsupp.basisSingleOne
-- #check Finsupp.single (2: Fin 3) 1
-- #check (Finsupp.single (2: Fin 3) 1) 3
-- example : (Finsupp.single (2: Fin 3) 1) 3 = 0 := by
--   simp

example (i : ι) : Finsupp.basisSingleOne i = Finsupp.single i 1 :=
  rfl

example [Finite ι] (x : ι → K) (i : ι) : (Pi.basisFun K ι).repr x i = x i := by
  simp

example [Fintype ι] : ∑ i : ι, B.repr v i • (B i) = v :=
  B.sum_repr v


example (c : ι →₀ K) (f : ι → V) (s : Finset ι) (h : c.support ⊆ s) :
    Finsupp.linearCombination K f c = ∑ i ∈ s, c i • f i :=
  Finsupp.linearCombination_apply_of_mem_supported K h

example : Finsupp.linearCombination K B (B.repr v) = v :=
  B.linearCombination_repr v

variable (f : ι → V) in

-- #check (Finsupp.linearCombination K f : (ι →₀ K) →ₗ[K] V)


section

variable {W : Type*} [AddCommGroup W] [Module K W]
         (φ : V →ₗ[K] W) (u : ι → W)

-- #check (B.constr K : (ι → W) ≃ₗ[K] (V →ₗ[K] W))
-- #check (B.constr K u : V →ₗ[K] W)

example (i : ι) : B.constr K u (B i) = u i :=
  B.constr_basis K u i

-- variable (φ : V →ₗ[K] W)
-- #check φ (B i)

example (φ ψ : V →ₗ[K] W) (h : ∀ i, φ (B i) = ψ (B i)) : φ = ψ :=
  B.ext h


variable {ι' : Type*} (B' : Basis ι' K W) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

open LinearMap

-- #check (toMatrix B B' : (V →ₗ[K] W) ≃ₗ[K] Matrix ι' ι K)

open Matrix -- get access to the ``*ᵥ`` notation for multiplication between matrices and vectors.

example (φ : V →ₗ[K] W) (v : V) : (toMatrix B B' φ) *ᵥ (B.repr v) = B'.repr (φ v) :=
  toMatrix_mulVec_repr B B' φ v


variable {ι'' : Type*} (B'' : Basis ι'' K W) [Fintype ι''] [DecidableEq ι'']

example (φ : V →ₗ[K] W) : (toMatrix B B'' φ) = (toMatrix B' B'' .id) * (toMatrix B B' φ) := by
  simp

end


open Module LinearMap Matrix

-- Some lemmas coming from the fact that `LinearMap.toMatrix` is an algebra morphism.
-- #check toMatrix_comp
-- #check id_comp
-- #check comp_id
-- #check toMatrix_id

-- Some lemmas coming from the fact that ``Matrix.det`` is a multiplicative monoid morphism.
-- #check Matrix.det_mul
-- #check Matrix.det_one

example [Fintype ι] (B' : Basis ι K V) (φ : End K V) :
    (toMatrix B B φ).det = (toMatrix B' B' φ).det := by
  set M := toMatrix B B φ
  set M' := toMatrix B' B' φ
  set P := (toMatrix B B') LinearMap.id
  set P' := (toMatrix B' B) LinearMap.id
  have h : M' = P * M * P' := by
    rw [<-toMatrix_comp]
    simp
    repeat rw [<-toMatrix_comp]
    rw [comp_id]
  rw [h]
  repeat rw [Matrix.det_mul]
  dsimp [P, P']
  nth_rewrite 1 [mul_comm]
  rw [<-mul_assoc]
  rw [<-Matrix.det_mul]
  have h' : ((toMatrix B' B) LinearMap.id * (toMatrix B B') LinearMap.id) = 1 := by
    rw [<-toMatrix_comp]
    rw [id_comp]
    rw [toMatrix_id]
  rw [h']
  rw [Matrix.det_one]
  norm_num
end

section
-- #check (Module.finrank K V : ℕ)

-- `Fin n → K` is the archetypical space with dimension `n` over `K`.
example (n : ℕ) : Module.finrank K (Fin n → K) = n :=
  Module.finrank_fin_fun K

-- Seen as a vector space over itself, `ℂ` has dimension one.
example : Module.finrank ℂ ℂ = 1 :=
  Module.finrank_self ℂ

-- But as a real vector space it has dimension two.
example : Module.finrank ℝ ℂ = 2 :=
  Complex.finrank_real_complex

example : Module.finrank ℂ (Fin 1 → ℂ) = 1 := by
  simp

example : Module.finrank ℂ (Fin 2 → ℂ) = 2 := by
  simp

example [FiniteDimensional K V] : 0 < Module.finrank K V ↔ Nontrivial V :=
  Module.finrank_pos_iff


example [FiniteDimensional K V] (h : 0 < Module.finrank K V) : Nontrivial V := by
  -- apply (Module.finrank_pos_iff (R := K)).1
  -- exact h
  rw [Module.finrank_pos_iff] at h
  exact h

variable {ι : Type*} (B : Basis ι K V)

example [Finite ι] : FiniteDimensional K V := FiniteDimensional.of_fintype_basis B

example [FiniteDimensional K V] : Finite ι :=
  (FiniteDimensional.fintypeBasisIndex B).finite

end

section

variable (E F : Submodule K V) [FiniteDimensional K V]

open Module

example : finrank K (E ⊔ F : Submodule K V) + finrank K (E ⊓ F : Submodule K V) =
    finrank K E + finrank K F :=
  Submodule.finrank_sup_add_finrank_inf_eq E F

example : finrank K E ≤ finrank K V := Submodule.finrank_le E

example (h : finrank K V < finrank K E + finrank K F) :
    Nontrivial (E ⊓ F : Submodule K V) := by
  have h_inf : 0 < Module.finrank K (E ⊓ F : Submodule K V) := by
    by_contra nonpos_rank_E_inf_F
    have zero_rank_E_inf_F : 0 = finrank K (E ⊓ F : Submodule K V) := by
      apply le_antisymm
      · exact Nat.zero_le (finrank K ↥(E ⊓ F))
      · rw [not_lt] at nonpos_rank_E_inf_F
        exact nonpos_rank_E_inf_F
    rw [<-Submodule.finrank_sup_add_finrank_inf_eq] at h
    rw [<-zero_rank_E_inf_F] at h
    simp at h
    have h_sup : finrank K (E ⊔ F : Submodule K V) ≤ finrank K V := by
      apply Submodule.finrank_le
    rw [<-not_lt] at h_sup
    apply h_sup at h
    exact h
  rw [Module.finrank_pos_iff] at h_inf
  exact h_inf
end

-- variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

-- #check ℝ -- Type
-- #check ℂ -- Type
-- #check !![1,2] -- Matrix (Fin 1) (Fin 2) ℕ
-- #check Type -- Type 1
-- #check Type 1 -- Type 2
-- #check Type u_1 -- Type (u_1 + 1)

universe u v -- `u` and `v` will denote universe levels
-- #check v  -- Error: unknown identifier 'v'
-- #check Type v -- Type (v + 1)

variable {ι  : Type u} (B  : Basis ι  K V)
         {ι' : Type v} (B' : Basis ι' K V)

-- #check K -- Type u_1
-- #check V -- Type u_2
-- #check Module.rank K V -- Cardinal.{u_2}
-- #check Cardinal.{u} -- Type (u + 1)
-- #check Cardinal.{u_1} -- Type (u_1 + 1)

variable {α₁ α₂ : Type*}
variable (f : α₁ → α₂)

example (h: Function.Bijective f) : Cardinal.lift.{u_4, u_3} (Cardinal.mk α₁) = Cardinal.lift.{u_3, u_4} (Cardinal.mk α₂) := by
  apply Cardinal.lift_mk_eq'.mpr
  apply Equiv.ofBijective at h
  exact Nonempty.intro h

example : Cardinal.lift.{v, u} (.mk ι) = Cardinal.lift.{u, v} (.mk ι') :=
  mk_eq_mk_of_basis B B'

example [FiniteDimensional K V] :
    (Module.finrank K V : Cardinal) = Module.rank K V :=
  Module.finrank_eq_rank K V
