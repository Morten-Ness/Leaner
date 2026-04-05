import Mathlib

variable {α β γ : Type*}

variable [One α]

theorem recZeroCoe_one {M N : Type*} [One M] (f : M → N) (z : N) :
    recZeroCoe z f 1 = f 1 := rfl

