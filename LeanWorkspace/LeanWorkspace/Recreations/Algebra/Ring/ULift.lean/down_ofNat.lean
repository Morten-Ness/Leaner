import Mathlib

variable {R : Type u}

theorem down_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    down (ofNat(n) : ULift R) = ofNat(n) := rfl

