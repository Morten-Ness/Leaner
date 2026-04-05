import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

theorem coe_maxTrivHom_apply (f : M →ₗ⁅R,L⁆ N) (m : LieModule.maxTrivSubmodule R L M) :
    (LieModule.maxTrivHom f m : N) = f m := rfl

