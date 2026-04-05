import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

variable [Nontrivial R]

theorem charZero_of_expChar_one' [hq : ExpChar R 1] : CharZero R := by
  cases hq
  · assumption
  · exact False.elim (CharP.char_ne_one R 1 rfl)

