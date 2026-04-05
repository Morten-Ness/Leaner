import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem lcm_union [DecidableEq β] : (s₁ ∪ s₂).lcm f = GCDMonoid.lcm (s₁.lcm f) (s₂.lcm f) := Finset.induction_on s₁ (by rw [empty_union, Finset.lcm_empty, lcm_one_left, Finset.normalize_lcm])
    fun a s _ ih ↦ by rw [insert_union, Finset.lcm_insert, Finset.lcm_insert, ih, lcm_assoc]

