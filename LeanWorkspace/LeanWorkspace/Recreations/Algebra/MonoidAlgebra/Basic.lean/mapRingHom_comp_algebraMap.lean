import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Semiring C]
  [Algebra R A] [Algebra R B] [Algebra R C] [Monoid M] [Monoid N]

theorem mapRingHom_comp_algebraMap (f : R →+* S) :
    (mapRingHom (M := M) f).comp (algebraMap _ _) = (algebraMap _ _).comp f := by ext; simp

