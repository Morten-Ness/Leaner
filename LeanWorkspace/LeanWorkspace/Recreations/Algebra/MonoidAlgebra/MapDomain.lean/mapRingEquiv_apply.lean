import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Monoid M] [Monoid N] [Monoid O]

theorem mapRingEquiv_apply (e : R ≃+* S) (x : R[M]) (m : M) :
    MonoidAlgebra.mapRingEquiv M e x m = e (x m) := by simp [MonoidAlgebra.mapRingEquiv]

