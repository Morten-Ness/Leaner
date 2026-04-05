import Mathlib

variable {R A : Type*}

variable (R : Type*) [Nontrivial R]

theorem algebraRat.charP_zero [Semiring R] [Algebra ℚ R] : CharP R 0 := charP_of_injective_algebraMap (algebraMap ℚ R).injective 0

