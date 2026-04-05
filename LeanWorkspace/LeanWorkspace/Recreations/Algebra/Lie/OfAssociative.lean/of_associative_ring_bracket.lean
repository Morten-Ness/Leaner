import Mathlib

variable {A : Type v} [Ring A]

theorem of_associative_ring_bracket (x y : A) : ⁅x, y⁆ = x * y - y * x := rfl

