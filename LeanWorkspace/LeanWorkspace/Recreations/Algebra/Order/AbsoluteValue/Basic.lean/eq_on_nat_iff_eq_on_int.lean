import Mathlib

variable {ι α R S : Type*}

variable [CommRing S] [PartialOrder S] [IsOrderedRing S] [Ring R]
  (abv : AbsoluteValue R S) [NoZeroDivisors S]

theorem eq_on_nat_iff_eq_on_int {f g : AbsoluteValue R S} :
    (∀ n : ℕ, f n = g n) ↔ ∀ n : ℤ, f n = g n := by
  refine ⟨fun h z ↦ ?_, fun a n ↦ mod_cast a n⟩
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z <;> simp [h n]

