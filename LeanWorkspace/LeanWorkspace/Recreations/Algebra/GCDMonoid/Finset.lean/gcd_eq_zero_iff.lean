import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_eq_zero_iff : s.gcd f = 0 ↔ ∀ x ∈ s, f x = 0 := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s h ih => grind [Finset.gcd_cons, _root_.gcd_eq_zero_iff]

