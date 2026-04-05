import Mathlib

variable {R A B C : Type*}

theorem ofConv_injective : Function.Injective (@ofConv A) := Function.LeftInverse.injective toConv_ofConv

