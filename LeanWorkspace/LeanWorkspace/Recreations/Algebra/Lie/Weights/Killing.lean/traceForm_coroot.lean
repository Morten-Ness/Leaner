import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

theorem traceForm_coroot (α : Weight K H L) (x : H) :
    traceForm K H L (LieAlgebra.IsKilling.coroot α) x = 2 • (α <| (LieAlgebra.IsKilling.cartanEquivDual H).symm α)⁻¹ • α x := by
  have : LieAlgebra.IsKilling.cartanEquivDual H ((LieAlgebra.IsKilling.cartanEquivDual H).symm α) x = α x := by
    rw [LinearEquiv.apply_symm_apply, Weight.toLinear_apply]
  rw [LieAlgebra.IsKilling.coroot, map_nsmul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply]
  congr 2

