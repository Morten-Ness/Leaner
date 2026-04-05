import Mathlib

variable {m n : ℤ}

theorem even_xor'_odd' (n : ℤ) : ∃ k, Xor' (n = 2 * k) (n = 2 * k + 1) := by
  rcases Int.even_or_odd n with (⟨k, rfl⟩ | ⟨k, rfl⟩) <;>
  · use k
    grind

