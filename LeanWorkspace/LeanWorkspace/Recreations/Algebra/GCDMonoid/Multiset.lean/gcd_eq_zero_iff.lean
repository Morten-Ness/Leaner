import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem gcd_eq_zero_iff (s : Multiset α) : s.gcd = 0 ↔ ∀ x ∈ s, x = 0 := by
  constructor
  · intro h x hx
    apply eq_zero_of_zero_dvd
    rw [← h]
    apply Multiset.gcd_dvd hx
  · refine s.induction_on ?_ ?_
    · simp
    intro a s sgcd h
    simp [h a (mem_cons_self a s), sgcd fun x hx ↦ h x (mem_cons_of_mem hx)]

