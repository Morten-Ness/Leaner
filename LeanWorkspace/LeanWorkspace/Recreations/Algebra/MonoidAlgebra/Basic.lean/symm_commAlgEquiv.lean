import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

theorem symm_commAlgEquiv : (MonoidAlgebra.commAlgEquiv R : A[M][N] ≃ₐ[R] A[N][M]).symm = MonoidAlgebra.commAlgEquiv R := rfl

