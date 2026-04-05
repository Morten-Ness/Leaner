import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']

variable (f : L →ₗ⁅R⁆ L') (I I₂ : LieIdeal R L) (J : LieIdeal R L')

theorem comap_toSubmodule :
    (LieSubmodule.toSubmodule (LieIdeal.comap f J)) = (LieSubmodule.toSubmodule J).comap (f : L →ₗ[R] L') := rfl

