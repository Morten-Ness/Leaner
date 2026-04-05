import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

theorem ofCoeff_mapRange (f : R →+ S) (x : M →₀ R) :
    ofCoeff (.mapRange f f.map_zero x) = MonoidAlgebra.map f (ofCoeff x) := rfl

