import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem inr_neg [AddGroup R] [Neg A] (m : A) : (↑(-m) : Unitization R A) = -m := Unitization.ext neg_zero.symm rfl

