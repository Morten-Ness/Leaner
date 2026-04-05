import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable [LieAlgebra R L] [LieModule R L M]

theorem LieIdeal.coe_bracket_of_module {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) [LieRingModule L M] (x : I) (m : M) :
    ⁅x, m⁆ = ⁅(↑x : L), m⁆ := LieSubalgebra.coe_bracket_of_module (I : LieSubalgebra R L) x m

