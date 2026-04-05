import Mathlib

variable {F α β : Type*}

variable [Monoid α] {n : ℕ} {a : α}

theorem IsSquare.sq (r : α) : IsSquare (r ^ 2) := ⟨r, pow_two _⟩

