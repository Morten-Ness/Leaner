import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Monoid M] [Monoid N] [Monoid O]

theorem mapRingHom_apply (f : R →+* S) (x : R[M]) (m : M) :
    MonoidAlgebra.mapRingHom M f x m = f (x m) := by simp [MonoidAlgebra.mapRingHom, MonoidAlgebra.map, coeff, ofCoeff]

