import Mathlib

variable {α : Type*}

variable [Semigroup α] {a b c : α}

theorem mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c := by
  obtain ⟨d, rfl⟩ := h
  use d
  rw [mul_assoc]

