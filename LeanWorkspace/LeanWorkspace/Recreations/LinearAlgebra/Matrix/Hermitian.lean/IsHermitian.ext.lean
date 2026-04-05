import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable [Star α] [Star β]

theorem IsHermitian.ext {A : Matrix n n α} : (∀ i j, star (A j i) = A i j) → A.IsHermitian := by
  intro h; ext i j; exact h i j

