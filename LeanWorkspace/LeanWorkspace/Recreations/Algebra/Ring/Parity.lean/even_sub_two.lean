import Mathlib

variable {F α β : Type*}

variable [Ring α] {a b : α} {n : ℕ}

theorem even_sub_two : Even (a - 2) ↔ Even a := ⟨(by convert ·.add even_two; rw [sub_add_cancel]), (·.sub even_two)⟩

