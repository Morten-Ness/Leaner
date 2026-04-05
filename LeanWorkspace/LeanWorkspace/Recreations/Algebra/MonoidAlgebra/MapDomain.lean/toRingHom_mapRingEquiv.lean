import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Monoid M] [Monoid N] [Monoid O]

theorem toRingHom_mapRingEquiv (e : R ≃+* S) :
    (MonoidAlgebra.mapRingEquiv M e).toRingHom = MonoidAlgebra.mapRingHom M e := rfl

