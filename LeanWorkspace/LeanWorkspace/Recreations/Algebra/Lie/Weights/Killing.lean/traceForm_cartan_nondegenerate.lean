import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [IsKilling R L]

theorem traceForm_cartan_nondegenerate
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    (LieModule.traceForm R H L).Nondegenerate := by
  simp [LinearMap.separatingLeft_iff_ker_eq_bot,
    (LieModule.traceForm_isSymm R H L).isRefl.nondegenerate_iff_separatingLeft]

