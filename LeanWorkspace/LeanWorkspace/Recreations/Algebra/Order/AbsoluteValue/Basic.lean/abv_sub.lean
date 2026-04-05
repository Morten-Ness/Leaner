import Mathlib

variable {ι α R S : Type*}

variable [CommRing S] [PartialOrder S] [IsOrderedRing S] [NoZeroDivisors S] [Ring R]
  (abv : R → S) [IsAbsoluteValue abv]

theorem abv_sub (a b : R) : abv (a - b) = abv (b - a) := AbsoluteValue.map_sub (IsAbsoluteValue.toAbsoluteValue abv) a b

