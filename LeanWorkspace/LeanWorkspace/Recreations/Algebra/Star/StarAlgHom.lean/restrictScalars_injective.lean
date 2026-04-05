import Mathlib

variable (R : Type*) {S A B : Type*} [Monoid R] [Monoid S] [Star A] [Star B]
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [MulAction R S]
    [DistribMulAction S A] [DistribMulAction S B] [DistribMulAction R A] [DistribMulAction R B]
    [IsScalarTower R S A] [IsScalarTower R S B]

theorem restrictScalars_injective :
    Function.Injective (NonUnitalStarAlgHom.restrictScalars R : (A →⋆ₙₐ[S] B) → A →⋆ₙₐ[R] B) := fun _ _ h ↦ NonUnitalStarAlgHom.ext (DFunLike.congr_fun h :)

