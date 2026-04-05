import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem lcm_eq_zero_iff [Nontrivial α] : s.lcm f = 0 ↔ ∃ x ∈ s, f x = 0 := by
  simp only [Finset.lcm_def, Multiset.lcm_eq_zero_iff, Multiset.mem_map, mem_val]

