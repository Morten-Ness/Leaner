import Mathlib

variable {α : Type u} {R : Type v}

variable [NonAssocSemiring α]

theorem two_mul (n : α) : 2 * n = n + n := (congrArg₂ _ one_add_one_eq_two.symm rfl).trans <| (right_distrib 1 1 n).trans (by rw [one_mul])

