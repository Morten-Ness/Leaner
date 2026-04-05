import Mathlib

variable {α : Type*}

theorem untop₀_natCast [AddMonoidWithOne α] (n : ℕ) : WithTop.untop₀ (n : WithTop α) = n := rfl

