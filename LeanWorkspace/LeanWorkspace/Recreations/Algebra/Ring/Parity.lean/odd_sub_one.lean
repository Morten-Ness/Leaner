import Mathlib

variable {F α β : Type*}

variable [Ring α] {a b : α} {n : ℕ}

theorem odd_sub_one : Odd (a - 1) ↔ Even a := ⟨(by convert ·.add_odd odd_one; rw [sub_add_cancel]), (·.sub_odd odd_one)⟩

