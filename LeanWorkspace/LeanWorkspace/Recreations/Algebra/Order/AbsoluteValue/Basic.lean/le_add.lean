import Mathlib

variable {ι α R S : Type*}

variable [CommRing S] [PartialOrder S] [IsOrderedRing S] [Ring R]
  (abv : AbsoluteValue R S) [NoZeroDivisors S]

theorem le_add (a b : R) : abv a - abv b ≤ abv (a + b) := by
  simpa only [tsub_le_iff_right, add_neg_cancel_right, AbsoluteValue.map_neg abv] using AbsoluteValue.add_le abv (a + b) (-b)

