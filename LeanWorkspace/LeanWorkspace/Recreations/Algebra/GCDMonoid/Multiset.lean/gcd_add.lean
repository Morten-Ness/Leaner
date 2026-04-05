import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem gcd_add (s₁ s₂ : Multiset α) : (s₁ + s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd := Eq.trans (by simp [Multiset.gcd]) (fold_add _ _ _ _ _)

