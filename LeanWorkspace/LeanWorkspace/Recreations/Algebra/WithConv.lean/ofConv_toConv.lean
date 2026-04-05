import Mathlib

variable {R A B C : Type*}

theorem ofConv_toConv (x : A) : ofConv (toConv x) = x := rfl

