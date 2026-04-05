import Mathlib

variable {α : Type*}

variable [Monoid α] {a b c : α} {m n : ℕ}

theorem dvd_rfl : ∀ {a : α}, a ∣ a := fun {a} => dvd_refl a

