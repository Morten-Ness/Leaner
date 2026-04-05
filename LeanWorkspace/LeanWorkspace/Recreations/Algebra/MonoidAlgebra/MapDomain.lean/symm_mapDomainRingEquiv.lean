import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Monoid M] [Monoid N] [Monoid O]

theorem symm_mapDomainRingEquiv (e : M ≃* N) :
    (MonoidAlgebra.mapDomainRingEquiv R e).symm = MonoidAlgebra.mapDomainRingEquiv R e.symm := rfl

