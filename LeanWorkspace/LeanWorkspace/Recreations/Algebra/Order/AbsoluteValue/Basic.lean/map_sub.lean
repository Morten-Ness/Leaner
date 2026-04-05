import Mathlib

variable {ι α R S : Type*}

variable [CommRing S] [PartialOrder S] [IsOrderedRing S] [Ring R]
  (abv : AbsoluteValue R S) [NoZeroDivisors S]

theorem map_sub (a b : R) : abv (a - b) = abv (b - a) := by rw [← neg_sub, AbsoluteValue.map_neg abv]

