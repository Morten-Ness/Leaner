import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable [DecidableEq α]

theorem lcm_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm := by
  rw [← Multiset.lcm_dedup, dedup_ext.2, Multiset.lcm_dedup, Multiset.lcm_add]
  simp

