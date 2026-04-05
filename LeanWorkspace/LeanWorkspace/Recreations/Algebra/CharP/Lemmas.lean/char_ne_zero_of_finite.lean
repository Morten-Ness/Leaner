import Mathlib

variable {R S : Type*}

variable (R) [NonAssocRing R]

theorem char_ne_zero_of_finite (p : ℕ) [CharP R p] [Finite R] : p ≠ 0 := by
  rintro rfl
  haveI : CharZero R := charP_to_charZero R
  exact absurd Nat.cast_injective (not_injective_infinite_finite ((↑) : ℕ → R))

