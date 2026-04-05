import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Monoid M] [Monoid N] [Monoid O]

theorem mapDomainRingEquiv_single (e : M ≃* N) (r : R) (m : M) :
    MonoidAlgebra.mapDomainRingEquiv R e (single m r) = single (e m) r := by simp [MonoidAlgebra.mapDomainRingEquiv]

