import Mathlib

open scoped TensorProduct

variable {R : Type u} [CommRing R]

variable (R) (L : Type v) (M : Type w)

variable [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem toModuleHom_apply (x : L) (m : M) : LieModule.toModuleHom R L M (x ⊗ₜ m) = ⁅x, m⁆ := by
  simp only [LieModule.toModuleHom, TensorProduct.LieModule.liftLie_apply, LieModuleHom.coe_mk,
    LieHom.coe_toLinearMap, toEnd_apply_apply]

