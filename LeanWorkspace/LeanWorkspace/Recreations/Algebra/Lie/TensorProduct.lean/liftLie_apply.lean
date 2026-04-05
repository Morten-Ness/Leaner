import Mathlib

open scoped TensorProduct

variable {R : Type u} [CommRing R]

variable {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂} {Q : Type w₃}

variable [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable [AddCommGroup P] [Module R P] [LieRingModule L P] [LieModule R L P]

variable [AddCommGroup Q] [Module R Q] [LieRingModule L Q] [LieModule R L Q]

theorem liftLie_apply (f : M →ₗ⁅R,L⁆ N →ₗ[R] P) (m : M) (n : N) :
    TensorProduct.LieModule.liftLie R L M N P f (m ⊗ₜ n) = f m n := by
  simp only [TensorProduct.LieModule.coe_liftLie_eq_lift_coe, LieModuleHom.coe_toLinearMap, TensorProduct.LieModule.lift_apply]

