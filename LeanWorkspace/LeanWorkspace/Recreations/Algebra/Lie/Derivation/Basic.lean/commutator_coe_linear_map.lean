import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

variable {D1 D2 : LieDerivation R L L}

theorem commutator_coe_linear_map : ↑⁅D1, D2⁆ = ⁅(D1 : Module.End R L), (D2 : Module.End R L)⁆ := rfl

