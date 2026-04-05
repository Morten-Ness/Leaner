import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Semiring C]
  [Algebra R A] [Algebra R B] [Algebra R C] [Monoid M] [Monoid N]

theorem mapAlgHom_single (f : A →ₐ[R] B) (m : M) (a : A) :
    MonoidAlgebra.mapAlgHom M f (single m a) = single m (f a) := by
  classical ext; simp [single_apply, apply_ite f]

