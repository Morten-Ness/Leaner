import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Semiring C]
  [Algebra R A] [Algebra R B] [Algebra R C] [Monoid M] [Monoid N]

theorem mapDomainRingHom_comp_algebraMap (f : M →* N) :
    (mapDomainRingHom A f).comp (algebraMap R A[M]) = algebraMap R A[N] := by ext; simp

