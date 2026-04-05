import Mathlib

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']

variable (f : L →ₗ⁅R⁆ L') (I I₂ : LieIdeal R L) (J : LieIdeal R L')

theorem map_comap_le : LieIdeal.map f (LieIdeal.comap f J) ≤ J := by rw [LieIdeal.map_le_iff_le_comap]

