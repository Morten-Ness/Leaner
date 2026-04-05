import Mathlib

variable {R : Type u}

theorem up_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    up (ofNat(n) : R) = ofNat(n) := rfl

