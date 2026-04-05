import Mathlib

variable (R : Type*) {S A B : Type*} [Monoid R] [Monoid S] [Star A] [Star B]
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [MulAction R S]
    [DistribMulAction S A] [DistribMulAction S B] [DistribMulAction R A] [DistribMulAction R B]
    [IsScalarTower R S A] [IsScalarTower R S B]

theorem coe_restrictScalars (f : A →⋆ₙₐ[S] B) : (f.restrictScalars R : A →ₙ+* B) = f := rfl

