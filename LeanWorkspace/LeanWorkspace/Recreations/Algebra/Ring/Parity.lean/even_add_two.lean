import Mathlib

variable {F α β : Type*}

variable [Ring α] {a b : α} {n : ℕ}

theorem even_add_two : Even (a + 2) ↔ Even a := ⟨(by convert ·.sub even_two; rw [eq_sub_iff_add_eq]), (·.add even_two)⟩

