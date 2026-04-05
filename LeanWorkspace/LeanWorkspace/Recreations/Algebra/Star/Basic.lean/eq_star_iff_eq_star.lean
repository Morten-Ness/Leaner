import Mathlib

open scoped Ring

variable {R : Type u}

theorem eq_star_iff_eq_star [InvolutiveStar R] {r s : R} : r = star s ↔ s = star r := ⟨eq_star_of_eq_star, eq_star_of_eq_star⟩

