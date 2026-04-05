import Mathlib

variable {R A B C : Type*}

theorem ofConv_surjective : Function.Surjective (@ofConv A) := Function.RightInverse.surjective WithConv.ofConv_toConv

