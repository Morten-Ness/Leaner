import Mathlib

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable {R' : Type*} [Semiring R'] [MulSemiringAction R' A] [SMulCommClass R' R A]

theorem pointwise_smul_toSubmodule (m : R') (S : Subalgebra R A) :
    Subalgebra.toSubmodule (m • S) = m • Subalgebra.toSubmodule S := rfl

