import Mathlib

variable {R : Type*}

theorem unop_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    unop (ofNat(n) : Rᵐᵒᵖ) = ofNat(n) := rfl

