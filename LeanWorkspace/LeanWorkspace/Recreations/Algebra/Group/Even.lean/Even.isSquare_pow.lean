import Mathlib

variable {F α β : Type*}

variable [Monoid α] {n : ℕ} {a : α}

theorem Even.isSquare_pow (hn : Even n) : ∀ a : α, IsSquare (a ^ n) := by aesop (add simp pow_add)

