import Mathlib

open scoped Ring

variable {R : Type u}

theorem eq_star_of_eq_star [InvolutiveStar R] {r s : R} (h : r = star s) : s = star r := by
  simp [h]

