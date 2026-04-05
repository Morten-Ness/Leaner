import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

theorem mapDomain_injective (hf : Function.Injective f) : Function.Injective (mapDomain (R := R) f) :=
  Finsupp.mapDomain_injective hf

