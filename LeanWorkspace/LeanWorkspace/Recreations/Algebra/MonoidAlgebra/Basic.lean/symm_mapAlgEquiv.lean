import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Semiring C]
  [Algebra R A] [Algebra R B] [Algebra R C] [Monoid M] [Monoid N]

theorem symm_mapAlgEquiv (e : A ≃ₐ[R] B) :
    (MonoidAlgebra.mapAlgEquiv R M e).symm = MonoidAlgebra.mapAlgEquiv R M e.symm := rfl

