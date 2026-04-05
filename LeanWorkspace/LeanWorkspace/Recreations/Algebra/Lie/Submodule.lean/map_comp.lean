import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable (f : M →ₗ⁅R,L⁆ M') (N N₂ : LieSubmodule R L M) (N' : LieSubmodule R L M')

theorem map_comp
    {M'' : Type*} [AddCommGroup M''] [Module R M''] [LieRingModule L M''] {g : M' →ₗ⁅R,L⁆ M''} :
    N.map (g.comp f) = (N.map f).map g := SetLike.coe_injective <| by
    simp only [← Set.image_comp, coe_map, LieModuleHom.coe_comp]

