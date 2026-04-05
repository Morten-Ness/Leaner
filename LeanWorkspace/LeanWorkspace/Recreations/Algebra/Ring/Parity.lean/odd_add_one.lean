import Mathlib

variable {F α β : Type*}

variable [Ring α] {a b : α} {n : ℕ}

theorem odd_add_one : Odd (a + 1) ↔ Even a := ⟨(by convert ·.sub_odd odd_one; rw [eq_sub_iff_add_eq]), (·.add_one)⟩

