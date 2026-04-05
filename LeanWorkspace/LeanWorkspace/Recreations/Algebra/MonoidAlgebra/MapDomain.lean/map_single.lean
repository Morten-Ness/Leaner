import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

theorem map_single (f : R →+ S) (r : R) (m : M) : MonoidAlgebra.map f (single m r) = single m (f r) := mapRange_single (hf := f.map_zero)

