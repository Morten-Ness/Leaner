import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable (L' : LieSubalgebra R L)

variable {M : Type w} [AddCommGroup M] [LieRingModule L M]

variable {N : Type w₁} [AddCommGroup N] [LieRingModule L N] [Module R N]

theorem coe_bracket_of_module (x : L') (m : M) : ⁅x, m⁆ = ⁅(x : L), m⁆ := rfl

