import Mathlib

variable {R : Type*}

theorem ofDual_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    (ofDual (ofNat(n) : Rᵒᵈ)) = ofNat(n) := rfl

