import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

theorem ad_ker_eq_bot_of_hasTrivialRadical [HasTrivialRadical R L] : (ad R L).ker = ⊥ := by simp

