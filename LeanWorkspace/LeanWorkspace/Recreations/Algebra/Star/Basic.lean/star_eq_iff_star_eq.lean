import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_eq_iff_star_eq [InvolutiveStar R] {r s : R} : star r = s ↔ star s = r := eq_comm.trans <| eq_star_iff_eq_star.trans eq_comm

