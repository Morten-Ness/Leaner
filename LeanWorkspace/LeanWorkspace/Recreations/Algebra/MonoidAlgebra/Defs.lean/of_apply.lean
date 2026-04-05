import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R]

theorem of_apply [AddZeroClass M] (a : Multiplicative M) : AddMonoidAlgebra.of R M a = single a.toAdd 1 := rfl

