import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

theorem not_isSimple_of_subsingleton [Subsingleton L] :
    ¬ IsSimple R L := fun contra ↦ contra.non_abelian inferInstance

