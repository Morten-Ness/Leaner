import Mathlib

variable {R : Type*}

variable [Semigroup R] {a b : R}

theorem IsLeftRegular.of_mul (ab : IsLeftRegular (a * b)) : IsLeftRegular b := Function.Injective.of_comp (f := (a * ·)) (by rwa [comp_mul_left a b])

