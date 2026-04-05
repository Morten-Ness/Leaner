import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem even_or_odd' (n : ℕ) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := by
  simpa only [← two_mul, exists_or, Odd, Even] using Nat.even_or_odd n

