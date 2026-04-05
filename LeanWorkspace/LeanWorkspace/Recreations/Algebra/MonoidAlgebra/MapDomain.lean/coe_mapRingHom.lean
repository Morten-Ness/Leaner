import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Monoid M] [Monoid N] [Monoid O]

theorem coe_mapRingHom (f : R →+* S) : ⇑(MonoidAlgebra.mapRingHom M f) = MonoidAlgebra.map f := rfl

