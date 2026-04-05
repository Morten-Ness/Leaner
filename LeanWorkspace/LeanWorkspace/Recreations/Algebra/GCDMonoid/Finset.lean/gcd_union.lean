import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_union [DecidableEq β] : (s₁ ∪ s₂).gcd f = GCDMonoid.gcd (s₁.gcd f) (s₂.gcd f) := Finset.induction_on s₁ (by rw [empty_union, Finset.gcd_empty, gcd_zero_left, Finset.normalize_gcd])
    fun a s _ ih ↦ by rw [insert_union, Finset.gcd_insert, Finset.gcd_insert, ih, gcd_assoc]

