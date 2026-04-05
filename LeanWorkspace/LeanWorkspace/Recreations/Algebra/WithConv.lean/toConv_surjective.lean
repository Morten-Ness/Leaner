import Mathlib

variable {R A B C : Type*}

theorem toConv_surjective : Function.Surjective (@toConv A) := Function.RightInverse.surjective toConv_ofConv

