import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem extract_gcd' (f g : β → α) (hs : ∃ x, x ∈ s ∧ f x ≠ 0)
    (hg : ∀ b ∈ s, f b = s.gcd f * g b) : s.gcd g = 1 := ((mul_right_eq_self₀ (a := s.gcd f)).1 <| by
        conv_lhs => rw [← Finset.normalize_gcd, ← gcd_mul_left, ← Finset.gcd_congr rfl hg]).resolve_right <| by
    contrapose! hs
    exact Finset.gcd_eq_zero_iff.1 hs

