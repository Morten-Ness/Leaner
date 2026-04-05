import Mathlib

variable (R K L : Type*) [CommRing R] [Field K] [LieRing L] [LieAlgebra R L] [LieAlgebra K L]

variable [IsKilling R L]

theorem killingForm_nondegenerate :
    (killingForm R L).Nondegenerate := by
  refine (LieModule.traceForm_isSymm R L L).isRefl.nondegenerate_iff_separatingLeft.mpr ?_
  simp [LinearMap.separatingLeft_iff_ker_eq_bot]

