import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

theorem maxTrivEquiv_of_equiv_symm_eq_symm (e : M ≃ₗ⁅R,L⁆ N) :
    (LieModule.maxTrivEquiv e).symm = LieModule.maxTrivEquiv e.symm := rfl

