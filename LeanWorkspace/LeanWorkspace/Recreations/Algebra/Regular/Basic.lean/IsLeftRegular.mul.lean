import Mathlib

variable {R : Type*}

variable [Semigroup R] {a b : R}

theorem IsLeftRegular.mul (lra : IsLeftRegular a) (lrb : IsLeftRegular b) : IsLeftRegular (a * b) := show Function.Injective (((a * b) * ·)) from comp_mul_left a b ▸ lra.comp lrb

