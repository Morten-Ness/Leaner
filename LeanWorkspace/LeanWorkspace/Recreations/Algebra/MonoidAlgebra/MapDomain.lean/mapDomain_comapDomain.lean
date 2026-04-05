import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

theorem mapDomain_comapDomain {f : M → N} {x : R[N]} (hx : ↑x.coeff.support ⊆ Set.range f) (hf) :
    mapDomain f (MonoidAlgebra.comapDomain f hf x) = x := Finsupp.mapDomain_comapDomain _ hf _ hx

