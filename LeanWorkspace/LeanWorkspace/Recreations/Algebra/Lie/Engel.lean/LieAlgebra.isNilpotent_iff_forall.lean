import Mathlib

variable {R : Type u₁} {L : Type u₂} {L₂ : Type u₃} {M : Type u₄}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem LieAlgebra.isNilpotent_iff_forall [IsNoetherian R L] :
    LieRing.IsNilpotent L ↔ ∀ x, IsNilpotent <| LieAlgebra.ad R L x := LieModule.isNilpotent_iff_forall

