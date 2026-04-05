import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable [DecidableEq α]

theorem gcd_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).gcd = GCDMonoid.gcd a s.gcd := by
  rw [← Multiset.gcd_dedup, dedup_ext.2, Multiset.gcd_dedup, Multiset.gcd_cons]
  simp

