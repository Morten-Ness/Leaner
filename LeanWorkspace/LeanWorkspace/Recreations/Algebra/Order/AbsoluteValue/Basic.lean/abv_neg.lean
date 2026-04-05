import Mathlib

variable {ι α R S : Type*}

variable [CommRing S] [PartialOrder S] [IsOrderedRing S] [NoZeroDivisors S] [Ring R]
  (abv : R → S) [IsAbsoluteValue abv]

theorem abv_neg (a : R) : abv (-a) = abv a := AbsoluteValue.map_neg (IsAbsoluteValue.toAbsoluteValue abv) a

