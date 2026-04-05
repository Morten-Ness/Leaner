import Mathlib

variable {M : Type*}

theorem quot_out [Monoid M] (a : Associates M) : Associates.mk (Quot.out a) = a := by
  rw [← Associates.quot_mk_eq_mk, Quot.out_eq]

