import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']

variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

theorem range_eq_top : f.range = ⊤ ↔ Function.Surjective f := by
  rw [← LieSubalgebra.toSubmodule_inj, LieHom.range_toSubmodule, LieSubalgebra.top_toSubmodule]
  exact LinearMap.range_eq_top

