import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

variable [IsSimple R L]

theorem eq_top_of_isAtom (I : LieIdeal R L) (hI : IsAtom I) : I = ⊤ := isAtom_iff_eq_top.mp hI

