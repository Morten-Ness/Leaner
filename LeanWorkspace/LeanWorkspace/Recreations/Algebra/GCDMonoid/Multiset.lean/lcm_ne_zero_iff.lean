import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem lcm_ne_zero_iff [Nontrivial α] (s : Multiset α) : s.lcm ≠ 0 ↔ 0 ∉ s := not_congr (lcm_eq_zero_iff s)

