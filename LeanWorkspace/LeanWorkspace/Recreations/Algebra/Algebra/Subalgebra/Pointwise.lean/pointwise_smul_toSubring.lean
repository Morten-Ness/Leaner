import Mathlib

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable {R' : Type*} [Semiring R'] [MulSemiringAction R' A] [SMulCommClass R' R A]

theorem pointwise_smul_toSubring {R' R A : Type*} [Semiring R'] [CommRing R] [Ring A]
    [MulSemiringAction R' A] [Algebra R A] [SMulCommClass R' R A] (m : R') (S : Subalgebra R A) :
    (m • S).toSubring = m • S.toSubring := rfl

