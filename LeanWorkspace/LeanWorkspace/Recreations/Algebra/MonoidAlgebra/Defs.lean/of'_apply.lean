import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R]

theorem of'_apply (a : M) : AddMonoidAlgebra.of' R M a = single a 1 := rfl

