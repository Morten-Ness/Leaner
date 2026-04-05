import Mathlib

variable (R : Type*) [CommRing R] [IsReduced R] (p n : ℕ) [ExpChar R p]

theorem frobenius_inj : Function.Injective (frobenius R p) := iterateFrobenius_one (R := R) p ▸ iterateFrobenius_inj R p 1

