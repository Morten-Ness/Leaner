import Mathlib

variable {ι α R S : Type*}

variable {R S : Type*} [Ring R] [Ring S] [PartialOrder S] [IsOrderedRing S]
  (abv : AbsoluteValue R S)

theorem le_sub (a b : R) : abv a - abv b ≤ abv (a - b) := sub_le_iff_le_add.2 <| by simpa using AbsoluteValue.add_le abv (a - b) b

