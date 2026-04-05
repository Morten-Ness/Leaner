import Mathlib

variable (R : Type u₁) (L : Type u₂)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable {A : Type u₃} [Ring A] [Algebra R A] (f : L →ₗ⁅R⁆ A)

theorem lift_symm_apply (F : UniversalEnvelopingAlgebra R L →ₐ[R] A) :
    (UniversalEnvelopingAlgebra.lift R).symm F = (F : UniversalEnvelopingAlgebra R L →ₗ⁅R⁆ A).comp (UniversalEnvelopingAlgebra.ι R) := rfl

