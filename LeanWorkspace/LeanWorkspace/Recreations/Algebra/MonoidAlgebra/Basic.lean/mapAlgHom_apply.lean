import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Semiring C]
  [Algebra R A] [Algebra R B] [Algebra R C] [Monoid M] [Monoid N]

theorem mapAlgHom_apply (f : A →ₐ[R] B) (x : A[M]) (m : M) :
    MonoidAlgebra.mapAlgHom M f x m = f (x m) := mapRingHom_apply f.toRingHom x m

