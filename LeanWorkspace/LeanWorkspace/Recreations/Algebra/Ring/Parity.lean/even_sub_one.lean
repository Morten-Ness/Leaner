import Mathlib

variable {F α β : Type*}

variable [Ring α] {a b : α} {n : ℕ}

theorem even_sub_one : Even (a - 1) ↔ Odd a := ⟨(by convert ·.add_odd odd_one; rw [sub_add_cancel]), (·.sub_odd odd_one)⟩

