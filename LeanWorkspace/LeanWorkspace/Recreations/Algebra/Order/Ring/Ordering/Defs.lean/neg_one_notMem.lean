import Mathlib

variable (R : Type*) [CommRing R]

theorem neg_one_notMem (P : RingPreordering R) : -1 ∉ P := RingPreordering.neg_one_notMem' _

