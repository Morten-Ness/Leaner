import Mathlib

variable {ι α R S : Type*}

variable {S : Type*} [Ring S] [PartialOrder S]

variable {R : Type*} [Ring R] (abv : R → S) [IsAbsoluteValue abv]

theorem sub_abv_le_abv_sub [IsOrderedRing S] (a b : R) : abv a - abv b ≤ abv (a - b) := AbsoluteValue.le_sub (IsAbsoluteValue.toAbsoluteValue abv) a b

