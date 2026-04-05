import Mathlib

variable {R S : Type*}

variable [Semiring R]

theorem single_eq_C (r : R) : .single 0 r = Polynomial.C r := rfl

