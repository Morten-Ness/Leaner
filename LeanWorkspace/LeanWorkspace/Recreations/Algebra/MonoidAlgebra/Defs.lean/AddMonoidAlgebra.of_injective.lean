import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R]

theorem of_injective [Nontrivial R] [AddZeroClass M] : Function.Injective (AddMonoidAlgebra.of R M) := MonoidAlgebra.of_injective

