import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Semiring C]
  [Algebra R A] [Algebra R B] [Algebra R C] [Monoid M] [Monoid N]

theorem toRingHom_mapAlgHom (f : A →ₐ[R] B) :
    MonoidAlgebra.mapAlgHom M f = mapRingHom M f.toRingHom := rfl

