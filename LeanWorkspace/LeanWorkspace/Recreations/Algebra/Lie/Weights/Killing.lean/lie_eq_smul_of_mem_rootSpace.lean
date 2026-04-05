import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [PerfectField K]

theorem lie_eq_smul_of_mem_rootSpace {α : H → K} {x : L} (hx : x ∈ rootSpace H α) (h : H) :
    ⁅h, x⁆ = α h • x := by
  replace hx : x ∈ (ad K L h).maxGenEigenspace (α h) :=
    genWeightSpace_le_genWeightSpaceOf L h α hx
  rw [(LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra
    h.property).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
    Module.End.mem_eigenspace_iff] at hx
  simpa using hx

