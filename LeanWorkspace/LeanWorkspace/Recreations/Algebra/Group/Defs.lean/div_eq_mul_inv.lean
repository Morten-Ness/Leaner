import Mathlib

variable {G : Type*}

variable [DivInvMonoid G]

theorem div_eq_mul_inv (a b : G) : a / b = a * b⁻¹ := DivInvMonoid.div_eq_mul_inv _ _

alias division_def := div_eq_mul_inv

