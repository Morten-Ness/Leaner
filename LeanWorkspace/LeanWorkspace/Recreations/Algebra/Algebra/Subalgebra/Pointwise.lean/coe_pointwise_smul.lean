import Mathlib

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable {R' : Type*} [Semiring R'] [MulSemiringAction R' A] [SMulCommClass R' R A]

theorem coe_pointwise_smul (m : R') (S : Subalgebra R A) : ↑(m • S) = m • (S : Set A) := rfl

