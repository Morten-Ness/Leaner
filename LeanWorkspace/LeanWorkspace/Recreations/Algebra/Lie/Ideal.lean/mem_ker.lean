import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']

variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

theorem mem_ker {x : L} : x ∈ LieHom.ker f ↔ f x = 0 := show x ∈ LieSubmodule.toSubmodule (f.ker) ↔ _ by
    simp only [LieHom.ker_toSubmodule, LinearMap.mem_ker, coe_toLinearMap]

