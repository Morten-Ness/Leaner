import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [IsCancelMulZero α] {a b : α} {m n : ℕ}

variable [Subsingleton αˣ]

theorem dvd_antisymm : a ∣ b → b ∣ a → a = b := by
  rintro ⟨c, rfl⟩ ⟨d, hcd⟩
  rw [mul_assoc, eq_comm, mul_right_eq_self₀, mul_eq_one] at hcd
  obtain ⟨rfl, -⟩ | rfl := hcd <;> simp

