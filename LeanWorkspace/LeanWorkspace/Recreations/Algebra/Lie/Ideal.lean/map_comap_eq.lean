import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']

variable {f : L →ₗ⁅R⁆ L'} {I I₂ : LieIdeal R L} {J : LieIdeal R L'}

theorem map_comap_eq (h : f.IsIdealMorphism) : LieIdeal.map f (LieIdeal.comap f J) = f.idealRange ⊓ J := by
  apply le_antisymm
  · rw [le_inf_iff]; exact ⟨LieHom.map_le_idealRange f _, LieIdeal.map_comap_le⟩
  · rw [LieHom.isIdealMorphism_def f] at h
    rw [← SetLike.coe_subset_coe, LieSubmodule.coe_inf, ← coe_toLieSubalgebra, h]
    rintro y ⟨⟨x, h₁⟩, h₂⟩; rw [← h₁] at h₂ ⊢; exact LieIdeal.mem_map h₂

