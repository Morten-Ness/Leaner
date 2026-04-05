import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem even_xor_odd' (n : ℕ) : ∃ k, Xor' (n = 2 * k) (n = 2 * k + 1) := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Nat.even_or_odd n <;>
  · use k
    grind

