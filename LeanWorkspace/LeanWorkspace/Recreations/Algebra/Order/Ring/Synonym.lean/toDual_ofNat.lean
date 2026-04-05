import Mathlib

variable {R : Type*}

theorem toDual_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    (toDual (ofNat(n) : R)) = ofNat(n) := rfl

