import Mathlib

variable {X : Type*}

theorem support_of (x : X) : FreeAbelianGroup.support (of x) = {x} := by
  rw [FreeAbelianGroup.support, toFinsupp_of, Finsupp.support_single_ne_zero _ one_ne_zero]

