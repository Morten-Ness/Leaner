import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [IsCancelMulZero α] {a b : α} {m n : ℕ}

variable [Subsingleton αˣ]

theorem dvd_antisymm' : a ∣ b → b ∣ a → b = a := flip dvd_antisymm

alias Dvd.dvd.antisymm := dvd_antisymm

alias Dvd.dvd.antisymm' := dvd_antisymm'

