import Mathlib

variable {R : Type u₁} {L : Type u₂} {L₂ : Type u₃} {M : Type u₄}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem LieModule.isNilpotent_iff_forall [IsNoetherian R L] :
    LieModule.IsNilpotent L M ↔ ∀ x, _root_.IsNilpotent <| toEnd R L M x := ⟨fun _ ↦ isNilpotent_toEnd_of_isNilpotent R L M,
   fun h => LieAlgebra.isEngelian_of_isNoetherian M h⟩

