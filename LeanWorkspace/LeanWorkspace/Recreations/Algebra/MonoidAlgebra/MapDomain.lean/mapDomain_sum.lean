import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

theorem mapDomain_sum (f : M → N) (x : S[M]) (v : M → S → R[M]) :
    mapDomain f (x.sum v) = x.sum fun a b ↦ mapDomain f (v a b) := Finsupp.mapDomain_sum

