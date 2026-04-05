import Mathlib

variable {R A B C : Type*}

theorem symm_congr_apply (f : A ≃ B) (x : WithConv B) :
    (WithConv.congr f).symm x = toConv (f.symm x.ofConv) := by simp

