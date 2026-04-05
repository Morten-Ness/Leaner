import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable (f : M →ₗ⁅R,L⁆ M') (N N₂ : LieSubmodule R L M) (N' : LieSubmodule R L M')

theorem map_injective_of_injective (hf : Function.Injective f) :
    Function.Injective (LieSubmodule.map f) := fun {N N'} h ↦
  SetLike.coe_injective <| hf.image_injective <| by simp only [← coe_map, h]

