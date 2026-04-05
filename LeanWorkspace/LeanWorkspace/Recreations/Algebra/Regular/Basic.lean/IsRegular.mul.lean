import Mathlib

variable {R : Type*}

variable [Semigroup R] {a b : R}

theorem IsRegular.mul (rra : IsRegular a) (rrb : IsRegular b) :
    IsRegular (a * b) := ⟨rra.left.mul rrb.left, rra.right.mul rrb.right⟩

