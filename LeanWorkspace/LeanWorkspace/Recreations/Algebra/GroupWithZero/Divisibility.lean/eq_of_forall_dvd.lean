import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [IsCancelMulZero α] {a b : α} {m n : ℕ}

variable [Subsingleton αˣ]

theorem eq_of_forall_dvd (h : ∀ c, a ∣ c ↔ b ∣ c) : a = b := ((h _).2 dvd_rfl).antisymm <| (h _).1 dvd_rfl

