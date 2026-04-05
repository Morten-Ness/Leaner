import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

variable [Nontrivial R]

theorem char_zero_of_expChar_one (p : ℕ) [hp : CharP R p] [hq : ExpChar R 1] : p = 0 := by
  cases hq
  · exact CharP.eq R hp (.ofCharZero R)
  · exact False.elim (CharP.char_ne_one R 1 rfl)

-- This could be an instance, but there are no `ExpChar R 1` instances in mathlib.

