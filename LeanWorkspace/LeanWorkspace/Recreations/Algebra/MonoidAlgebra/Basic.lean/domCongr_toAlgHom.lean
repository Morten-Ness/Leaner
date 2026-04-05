import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

theorem domCongr_toAlgHom (e : M ≃* N) : (MonoidAlgebra.domCongr R A e).toAlgHom = MonoidAlgebra.mapDomainAlgHom R A e := rfl

