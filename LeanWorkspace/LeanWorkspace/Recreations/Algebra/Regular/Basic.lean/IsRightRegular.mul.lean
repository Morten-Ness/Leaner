import Mathlib

variable {R : Type*}

variable [Semigroup R] {a b : R}

theorem IsRightRegular.mul (rra : IsRightRegular a) (rrb : IsRightRegular b) :
    IsRightRegular (a * b) := show Function.Injective (· * (a * b)) from comp_mul_right b a ▸ rrb.comp rra

