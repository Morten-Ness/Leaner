import Mathlib

variable {ι α R S : Type*}

variable [CommRing S] [PartialOrder S] [IsOrderedRing S] [Ring R]
  (abv : AbsoluteValue R S) [NoZeroDivisors S]

theorem apply_natAbs_eq (x : ℤ) : abv (natAbs x) = abv x := by
  obtain ⟨_, rfl | rfl⟩ := Int.eq_nat_or_neg x <;> simp

