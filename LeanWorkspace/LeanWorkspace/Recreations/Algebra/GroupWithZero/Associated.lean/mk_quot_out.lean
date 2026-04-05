import Mathlib

variable {M : Type*}

theorem mk_quot_out [Monoid M] (a : M) : Quot.out (Associates.mk a) ~ᵤ a := by
  rw [← Associates.mk_eq_mk_iff_associated, Associates.quot_out]

