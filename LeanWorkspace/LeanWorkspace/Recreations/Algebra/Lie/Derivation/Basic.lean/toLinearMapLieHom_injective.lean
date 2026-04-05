import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

theorem toLinearMapLieHom_injective : Function.Injective (LieDerivation.toLinearMapLieHom R L) := fun _ _ h ↦ LieDerivation.ext fun a ↦ congrFun (congrArg DFunLike.coe h) a

