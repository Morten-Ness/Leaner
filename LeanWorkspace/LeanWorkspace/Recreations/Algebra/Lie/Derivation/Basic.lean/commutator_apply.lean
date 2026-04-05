import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

variable {D1 D2 : LieDerivation R L L}

theorem commutator_apply (a : L) : ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a) := rfl

