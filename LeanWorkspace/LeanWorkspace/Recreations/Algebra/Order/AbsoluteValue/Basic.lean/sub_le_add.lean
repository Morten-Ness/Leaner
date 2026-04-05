import Mathlib

variable {ι α R S : Type*}

variable [CommRing S] [PartialOrder S] [IsOrderedRing S] [Ring R]
  (abv : AbsoluteValue R S) [NoZeroDivisors S]

theorem sub_le_add (a b : R) : abv (a - b) ≤ abv a + abv b := by
  simpa only [← sub_eq_add_neg, AbsoluteValue.map_neg] using AbsoluteValue.add_le abv a (-b)

