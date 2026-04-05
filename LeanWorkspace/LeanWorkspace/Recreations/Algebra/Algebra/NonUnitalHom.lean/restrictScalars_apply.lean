import Mathlib

variable {R : Type u} {S : Type u₁}

variable (R : Type*) {S A B : Type*} [Monoid R] [Monoid S]
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [MulAction R S]
    [DistribMulAction S A] [DistribMulAction S B] [DistribMulAction R A] [DistribMulAction R B]
    [IsScalarTower R S A] [IsScalarTower R S B]

theorem restrictScalars_apply (f : A →ₙₐ[S] B) (x : A) : f.restrictScalars R x = f x := rfl

