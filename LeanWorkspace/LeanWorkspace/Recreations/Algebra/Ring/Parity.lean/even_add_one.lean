import Mathlib

variable {F α β : Type*}

variable [Ring α] {a b : α} {n : ℕ}

theorem even_add_one : Even (a + 1) ↔ Odd a := ⟨(by convert ·.sub_odd odd_one; rw [eq_sub_iff_add_eq]), (·.add_one)⟩

