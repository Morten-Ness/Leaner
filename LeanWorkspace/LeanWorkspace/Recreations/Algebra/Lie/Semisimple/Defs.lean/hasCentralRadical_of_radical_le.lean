import Mathlib

variable (R L M : Type*)

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [LieAlgebra R L]

theorem hasCentralRadical_of_radical_le (h : radical R L ≤ center R L) :
    LieAlgebra.HasCentralRadical R L where
  radical_eq_center := le_antisymm h (center_le_radical R L)

