import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

theorem mapDomain_add (f : M → N) (x y : R[M]) :
    mapDomain f (x + y) = mapDomain f x + mapDomain f y := Finsupp.mapDomain_add ..

