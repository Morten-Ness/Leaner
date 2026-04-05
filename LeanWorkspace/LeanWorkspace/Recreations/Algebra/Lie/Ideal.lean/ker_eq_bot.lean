import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']

variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

theorem ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f := by
  rw [← LieSubmodule.toSubmodule_inj, LieHom.ker_toSubmodule, LieSubmodule.bot_toSubmodule,
    LinearMap.ker_eq_bot, coe_toLinearMap]

