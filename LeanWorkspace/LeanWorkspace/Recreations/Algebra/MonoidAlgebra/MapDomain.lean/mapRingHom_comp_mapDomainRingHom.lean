import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Monoid M] [Monoid N] [Monoid O]

theorem mapRingHom_comp_mapDomainRingHom (f : R →+* S) (g : M →* N) :
    (MonoidAlgebra.mapRingHom N f).comp (MonoidAlgebra.mapDomainRingHom R g) =
      (MonoidAlgebra.mapDomainRingHom S g).comp (MonoidAlgebra.mapRingHom M f) := by aesop

