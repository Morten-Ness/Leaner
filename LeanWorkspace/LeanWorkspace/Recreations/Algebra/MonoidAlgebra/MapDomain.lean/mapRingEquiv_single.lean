import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Monoid M] [Monoid N] [Monoid O]

theorem mapRingEquiv_single (e : R ≃+* S) (r : R) (m : M) :
    MonoidAlgebra.mapRingEquiv M e (single m r) = single m (e r) := by simp [MonoidAlgebra.mapRingEquiv]

