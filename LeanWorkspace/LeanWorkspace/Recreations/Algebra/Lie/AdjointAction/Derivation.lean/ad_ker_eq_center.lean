import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

theorem ad_ker_eq_center : (LieDerivation.ad R L).ker = LieAlgebra.center R L := by
  ext x
  rw [← LieAlgebra.self_module_ker_eq_center, LieHom.mem_ker, LieModule.mem_ker]
  simp [DFunLike.ext_iff]

