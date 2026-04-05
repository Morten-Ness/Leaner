import Mathlib

variable {R N L M : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

theorem toKer_bracket [IsLieAbelian M] (E : LieAlgebra.Extension R M L) (x : E.proj.ker) (y : L) :
    letI := E.ringModuleOf
    E.toKer ⁅y, E.toKer.symm x⁆ = ⁅E.proj_surjective.hasRightInverse.choose y, x⁆ := by
  simp

