import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

theorem mapDomain_zero (f : M → N) : mapDomain f (0 : R[M]) = 0 := Finsupp.mapDomain_zero ..

