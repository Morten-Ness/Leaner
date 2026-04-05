import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

theorem toNonUnitalAlgHom_injective :
    Function.Injective (LieHom.toNonUnitalAlgHom : _ → CommutatorRing L →ₙₐ[R] CommutatorRing L₂) := fun _ _ h => ext <| NonUnitalAlgHom.congr_fun h

