import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R]

theorem of'_eq_of [AddZeroClass M] (a : M) : AddMonoidAlgebra.of' R M a = AddMonoidAlgebra.of R M (.ofAdd a) := rfl

