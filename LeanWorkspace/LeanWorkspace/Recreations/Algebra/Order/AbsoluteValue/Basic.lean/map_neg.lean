import Mathlib

variable {ι α R S : Type*}

variable [CommRing S] [PartialOrder S] [IsOrderedRing S] [Ring R]
  (abv : AbsoluteValue R S) [NoZeroDivisors S]

theorem map_neg (a : R) : abv (-a) = abv a := by
  by_cases ha : a = 0; · simp [ha]
  refine
    (mul_self_eq_mul_self_iff.mp (by rw [← AbsoluteValue.map_mul abv, neg_mul_neg, AbsoluteValue.map_mul abv])).resolve_right ?_
  exact ((neg_lt_zero.mpr (abv.pos ha)).trans (abv.pos (neg_ne_zero.mpr ha))).ne'

