import Mathlib

variable {α : Type u} {R : Type v}

variable [NonAssocSemiring α]

theorem mul_two (n : α) : n * 2 = n + n := (congrArg₂ _ rfl one_add_one_eq_two.symm).trans <| (left_distrib n 1 1).trans (by rw [mul_one])

