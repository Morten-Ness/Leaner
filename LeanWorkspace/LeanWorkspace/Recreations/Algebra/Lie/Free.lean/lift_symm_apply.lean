import Mathlib

variable (R : Type u) (X : Type v) [CommRing R]

variable {L : Type w} [LieRing L] [LieAlgebra R L]

theorem lift_symm_apply (F : FreeLieAlgebra R X →ₗ⁅R⁆ L) : (FreeLieAlgebra.lift R).symm F = F ∘ FreeLieAlgebra.of R := rfl

