import Mathlib

variable {ι α R S : Type*}

variable {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]

variable {R : Type*} [Ring R] (abv : R → S) [IsAbsoluteValue abv]

theorem abs_abv_sub_le_abv_sub (a b : R) : abs (abv a - abv b) ≤ abv (a - b) := AbsoluteValue.abs_abv_sub_le_abv_sub (IsAbsoluteValue.toAbsoluteValue abv) a b

