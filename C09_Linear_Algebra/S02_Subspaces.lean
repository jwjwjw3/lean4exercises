import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common


variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

example (U : Submodule K V) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    x + y ∈ U :=
  U.add_mem hx hy

example (U : Submodule K V) {x : V} (hx : x ∈ U) (a : K) :
    a • x ∈ U :=
  U.smul_mem a hx

-- #check Set.range Complex.ofReal'

noncomputable example : Submodule ℝ ℂ where
  carrier := Set.range ((↑) : ℝ → ℂ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  smul_mem' := by
    --proof 1
    -- intro a c hc
    -- rcases hc with ⟨C, HC⟩
    -- use a • C
    -- rw [<-HC]
    -- simp
    --proof 2
    rintro c - ⟨a, rfl⟩
    use c*a
    simp


def preimage {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W) (H : Submodule K W) :
    Submodule K V where
  carrier := φ ⁻¹' H
  zero_mem' := by
    dsimp
    rw [Set.mem_preimage, LinearMap.map_zero]
    exact zero_mem H
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_preimage] at ha
    rw [Set.mem_preimage] at hb
    rw [Set.mem_preimage]
    rw [map_add]
    apply add_mem ha hb
  smul_mem' := by
    dsimp
    intro k v H
    rw [Set.mem_preimage] at H
    rw [Set.mem_preimage]
    rw [map_smul]
    apply Submodule.smul_mem
    exact H

example (U : Submodule K V) : Module K U := inferInstance

example (U : Submodule K V) : Module K {x : V // x ∈ U} := inferInstance


example (H H' : Submodule K V) :
    ((H ⊓ H' : Submodule K V) : Set V) = (H : Set V) ∩ (H' : Set V) := rfl

example (H H' : Submodule K V) :
    ((H ⊔ H' : Submodule K V) : Set V) = Submodule.span K ((H : Set V) ∪ (H' : Set V)) := by
  simp [Submodule.span_union]

example (x : V) : x ∈ (⊤ : Submodule K V) := trivial

example (x : V) : x ∈ (⊥ : Submodule K V) ↔ x = 0 := Submodule.mem_bot K


-- If two subspaces are in direct sum then they span the whole space.
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊔ V = ⊤ := by
  apply h.sup_eq_top

-- If two subspaces are in direct sum then they intersect only at zero.
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊓ V = ⊥ := h.inf_eq_bot

section
open DirectSum
variable {ι : Type*} [DecidableEq ι]

-- #check DirectSum

-- If subspaces are in direct sum then they span the whole space.
example (U : ι → Submodule K V) (h : DirectSum.IsInternal U) :
  ⨆ i, U i = ⊤ := h.submodule_iSup_eq_top

-- If subspaces are in direct sum then they pairwise intersect only at zero.
example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V) (h : DirectSum.IsInternal U)
    {i j : ι} (hij : i ≠ j) : U i ⊓ U j = ⊥ :=
  (h.submodule_independent.pairwiseDisjoint hij).eq_bot

-- Those conditions characterize direct sums.
-- #check DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top

-- The relation with external direct sums: if a family of subspaces is
-- in internal direct sum then the map from their external direct sum into `V`
-- is a linear isomorphism.
noncomputable example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V)
    (h : DirectSum.IsInternal U) : (⨁ i, U i) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (coeLinearMap U) h
end


example {s : Set V} (E : Submodule K V) : Submodule.span K s ≤ E ↔ s ⊆ E :=
  Submodule.span_le

example : GaloisInsertion (Submodule.span K) ((↑) : Submodule K V → Set V) :=
  Submodule.gi K V

example {S T : Submodule K V} {x : V} (h : x ∈ S ⊔ T) :
    ∃ s ∈ S, ∃ t ∈ T, x = s + t  := by
  rw [← S.span_eq, ← T.span_eq, ← Submodule.span_union] at h
  apply Submodule.span_induction h (p := fun x ↦ ∃ s ∈ S, ∃ t ∈ T, x = s + t)
  · intro x₁ hx₁
    simp at hx₁
    rcases hx₁ with (hs | ht)
    · use x₁, hs, 0, T.zero_mem
      module
    · use 0, S.zero_mem, x₁, ht
      module
  · use 0, S.zero_mem, 0, T.zero_mem
    module
  · rintro - - ⟨s, hs, t, ht, rfl⟩ ⟨s', hs', t', ht', rfl⟩
    use s + s', S.add_mem hs hs', t + t', T.add_mem ht ht'
    module
  · rintro a - ⟨s, hs, t, ht, rfl⟩
    use a • s, S.smul_mem a hs, a • t, T.smul_mem a ht
    module


section


variable {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W)

variable (E : Submodule K V) in
-- #check (Submodule.map φ E : Submodule K W)

variable (F : Submodule K W) in
-- #check (Submodule.comap φ F : Submodule K V)

example : LinearMap.range φ = Submodule.map φ ⊤ := LinearMap.range_eq_map φ

example : LinearMap.range φ = .map φ ⊤ := LinearMap.range_eq_map φ

example : LinearMap.ker φ = Submodule.comap φ ⊥ := Submodule.comap_bot φ

example : LinearMap.ker φ = .comap φ ⊥ := Submodule.comap_bot φ -- or `rfl`


open Function LinearMap

example : Injective φ ↔ ker φ = ⊥ := ker_eq_bot.symm

example : Surjective φ ↔ range φ = ⊤ := range_eq_top.symm

-- #check Submodule.mem_map_of_mem
-- #check Submodule.mem_map
-- #check Submodule.mem_comap

example (E : Submodule K V) (F : Submodule K W) :
    Submodule.map φ E ≤ F ↔ E ≤ Submodule.comap φ F := by
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    apply h hx
  -- exact Submodule.map_le_iff_le_comap


variable (E : Submodule K V)

example : Module K (V ⧸ E) := inferInstance

example : V →ₗ[K] V ⧸ E := E.mkQ

example : ker E.mkQ = E := E.ker_mkQ

example : range E.mkQ = ⊤ := E.range_mkQ

example (hφ : E ≤ ker φ) : V ⧸ E →ₗ[K] W := E.liftQ φ hφ

example (F : Submodule K W) (hφ : E ≤ .comap φ F) : V ⧸ E →ₗ[K] W ⧸ F := E.mapQ F φ hφ

noncomputable example : (V ⧸ LinearMap.ker φ) ≃ₗ[K] range φ := φ.quotKerEquivRange


open Submodule

-- #check Submodule.map_comap_eq
-- #check Submodule.comap_map_eq

example : Submodule K (V ⧸ E) ≃ { F : Submodule K V // E ≤ F } where
  toFun F := ⟨Submodule.comap E.mkQ F, by
    conv_lhs => rw [← E.ker_mkQ, ← comap_bot]
    gcongr
    apply bot_le⟩
  invFun P := by
    apply Submodule.map E.mkQ P
  left_inv P := by
    dsimp
    rw [Submodule.map_comap_eq]
    rw [E.range_mkQ]
    exact top_inf_eq P
  right_inv P := by
    ext x
    dsimp
    rw [Submodule.comap_map_eq]
    rw [E.ker_mkQ]
    rw [sup_of_le_left]
    apply P.2
