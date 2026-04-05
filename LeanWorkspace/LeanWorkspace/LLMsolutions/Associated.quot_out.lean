import Mathlib

variable {M : Type*}

theorem quot_out [Monoid M] (a : Associates M) : Associates.mk (Quot.out a) = a := by
  exact Quot.out_eq a
