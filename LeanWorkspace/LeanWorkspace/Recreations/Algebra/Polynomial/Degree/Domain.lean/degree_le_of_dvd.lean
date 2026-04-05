import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

theorem degree_le_of_dvd (h1 : p ∣ q) (h2 : q ≠ 0) : degree p ≤ degree q := by
  rcases h1 with ⟨q, rfl⟩; rw [mul_ne_zero_iff] at h2
  exact degree_le_mul_left p h2.2

