import Mathlib

variable {R A B C : Type*}

theorem toConv_injective : Function.Injective (@toConv A) := Function.LeftInverse.injective WithConv.ofConv_toConv

