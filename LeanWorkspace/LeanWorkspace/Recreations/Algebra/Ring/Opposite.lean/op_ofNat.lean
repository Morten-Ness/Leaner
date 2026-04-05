import Mathlib

variable {R : Type*}

theorem op_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    op (ofNat(n) : R) = ofNat(n) := rfl

