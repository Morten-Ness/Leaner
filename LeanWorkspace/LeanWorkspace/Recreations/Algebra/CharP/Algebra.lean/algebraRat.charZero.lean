import Mathlib

variable {R A : Type*}

variable (R : Type*) [Nontrivial R]

theorem algebraRat.charZero [Ring R] [Algebra ℚ R] : CharZero R := @CharP.charP_to_charZero R _ (algebraRat.charP_zero R)

