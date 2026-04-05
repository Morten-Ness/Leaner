import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable [DecidableEq α]

theorem lcm_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).lcm = GCDMonoid.lcm a s.lcm := by
  rw [← Multiset.lcm_dedup, dedup_ext.2, Multiset.lcm_dedup, Multiset.lcm_cons]
  simp

