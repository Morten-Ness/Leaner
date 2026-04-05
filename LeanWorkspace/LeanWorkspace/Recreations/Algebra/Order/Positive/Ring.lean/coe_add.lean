import Mathlib

variable {M R : Type*}

variable [AddMonoid M] [Preorder M] [AddLeftStrictMono M]

theorem coe_add (x y : { x : M // 0 < x }) : ↑(x + y) = (x + y : M) := rfl

