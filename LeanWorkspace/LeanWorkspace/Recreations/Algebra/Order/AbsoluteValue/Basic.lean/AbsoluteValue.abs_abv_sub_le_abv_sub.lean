import Mathlib

variable {ι α R S : Type*}

variable {R S : Type*} [Ring R] [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
  (abv : AbsoluteValue R S)

theorem abs_abv_sub_le_abv_sub (a b : R) : abs (abv a - abv b) ≤ abv (a - b) := abs_sub_le_iff.2 ⟨AbsoluteValue.le_sub abv _ _, by rw [AbsoluteValue.map_sub abv]; apply AbsoluteValue.le_sub abv⟩

