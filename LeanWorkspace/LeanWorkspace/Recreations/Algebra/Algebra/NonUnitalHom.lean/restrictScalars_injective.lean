import Mathlib

variable {R : Type u} {S : Type u₁}

variable (R : Type*) {S A B : Type*} [Monoid R] [Monoid S]
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [MulAction R S]
    [DistribMulAction S A] [DistribMulAction S B] [DistribMulAction R A] [DistribMulAction R B]
    [IsScalarTower R S A] [IsScalarTower R S B]

theorem restrictScalars_injective :
    Function.Injective (NonUnitalAlgHom.restrictScalars R : (A →ₙₐ[S] B) → A →ₙₐ[R] B) := fun _ _ h ↦ NonUnitalAlgHom.ext (NonUnitalAlgHom.congr_fun h :)

