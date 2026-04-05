import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem Ring.inverse_eq_inv' : (Ring.inverse : G₀ → G₀) = Inv.inv := funext Ring.inverse_eq_inv

