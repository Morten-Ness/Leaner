import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem lcm_add (s₁ s₂ : Multiset α) : (s₁ + s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm := Eq.trans (by simp [Multiset.lcm]) (fold_add _ _ _ _ _)

