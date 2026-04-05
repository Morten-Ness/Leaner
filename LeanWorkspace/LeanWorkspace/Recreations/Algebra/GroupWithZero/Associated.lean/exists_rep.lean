import Mathlib

variable {M : Type*}

theorem exists_rep [Monoid M] (a : Associates M) : ∃ a0 : M, Associates.mk a0 = a := Quot.exists_rep a

