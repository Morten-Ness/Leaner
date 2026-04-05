import Mathlib

variable {F α β : Type*}

variable [Ring α] {a b : α} {n : ℕ}

theorem odd_sub_two : Odd (a - 2) ↔ Odd a := by
  rw [← odd_add_two (a := a - 2), add_comm_sub, sub_self, add_zero]

