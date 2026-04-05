import Mathlib

variable (R : Type u) (L : Type v)

variable [CommRing R] [LieRing L]

variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [LieAlgebra R L] [LieModule R L M]

theorem LieIdeal.topEquiv_apply (x : (⊤ : LieIdeal R L)) : LieIdeal.topEquiv x = x := rfl

