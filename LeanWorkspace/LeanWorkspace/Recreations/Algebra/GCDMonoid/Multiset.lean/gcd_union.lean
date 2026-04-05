import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable [DecidableEq α]

theorem gcd_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd := by
  rw [← Multiset.gcd_dedup, dedup_ext.2, Multiset.gcd_dedup, Multiset.gcd_add]
  simp

