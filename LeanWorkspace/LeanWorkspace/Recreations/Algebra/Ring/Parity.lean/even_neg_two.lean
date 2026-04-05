import Mathlib

variable {F α β : Type*}

variable [Ring α] {a b : α} {n : ℕ}

theorem even_neg_two : Even (-2 : α) := by simp only [even_neg, even_two]

