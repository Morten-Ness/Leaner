import Mathlib

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable {R' : Type*} [Semiring R'] [MulSemiringAction R' A] [SMulCommClass R' R A]

theorem pointwise_smul_toSubsemiring (m : R') (S : Subalgebra R A) :
    (m • S).toSubsemiring = m • S.toSubsemiring := rfl

