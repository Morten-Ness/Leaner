import Mathlib

variable {α : Type*}

variable [Monoid α] {a b c : α} {m n : ℕ}

theorem dvd_of_eq (h : a = b) : a ∣ b := by rw [h]

alias Eq.dvd := dvd_of_eq

