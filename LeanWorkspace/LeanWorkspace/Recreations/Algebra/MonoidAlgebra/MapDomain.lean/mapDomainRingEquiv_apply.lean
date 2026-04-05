import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Monoid M] [Monoid N] [Monoid O]

theorem mapDomainRingEquiv_apply (e : M ≃* N) (x : R[M]) (n : N) :
    MonoidAlgebra.mapDomainRingEquiv R e x n = x (e.symm n) := MonoidAlgebra.mapDomainAddEquiv_apply ..

