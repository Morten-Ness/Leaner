import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem dvd_gcd_iff {a : α} : a ∣ s.gcd f ↔ ∀ b ∈ s, a ∣ f b := by
  apply Iff.trans Multiset.dvd_gcd
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb ↦ k _ _ hb rfl, fun k a' b hb h ↦ h ▸ k _ hb⟩

