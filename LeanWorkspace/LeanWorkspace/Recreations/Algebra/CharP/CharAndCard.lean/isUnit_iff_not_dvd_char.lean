import Mathlib

theorem isUnit_iff_not_dvd_char (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [Finite R] :
    IsUnit (p : R) ↔ ¬p ∣ ringChar R := isUnit_iff_not_dvd_char_of_ringChar_ne_zero R p <| CharP.char_ne_zero_of_finite R (ringChar R)

