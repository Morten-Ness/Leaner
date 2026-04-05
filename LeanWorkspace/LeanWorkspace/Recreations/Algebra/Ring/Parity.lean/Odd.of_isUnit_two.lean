import Mathlib

variable {F α β : Type*}

variable [Ring α]

theorem Odd.of_isUnit_two (h : IsUnit (2 : α)) (a : α) : Odd a := by
  rw [← sub_add_cancel a 1]
  exact (Even.of_isUnit_two h _).add_one

