import Mathlib

variable {α : Type*}

theorem untop₀_ofNat [AddMonoidWithOne α] (n : ℕ) [n.AtLeastTwo] :
    WithTop.untop₀ (ofNat(n) : WithTop α) = ofNat(n) := rfl

