import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

theorem coeff_map (f : R →+ S) (x : R[M]) :
    (MonoidAlgebra.map f x).coeff = x.coeff.mapRange f f.map_zero := rfl

