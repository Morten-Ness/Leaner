import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem extract_gcd (f : β → α) (hs : s.Nonempty) :
    ∃ g : β → α, (∀ b ∈ s, f b = s.gcd f * g b) ∧ s.gcd g = 1 := by
  classical
    by_cases! h : ∀ x ∈ s, f x = (0 : α)
    · refine ⟨fun _ ↦ 1, fun b hb ↦ by rw [h b hb, Finset.gcd_eq_zero_iff.2 h, mul_one], ?_⟩
      rw [Finset.gcd_eq_gcd_image, image_const hs, Finset.gcd_singleton, id, normalize_one]
    · choose g' hg using @Finset.gcd_dvd _ _ _ _ s f
      refine ⟨fun b ↦ if hb : b ∈ s then g' hb else 0, fun b hb ↦ ?_,
          Finset.extract_gcd' f _ h fun b hb ↦ ?_⟩
      · simp only [hb, hg, dite_true]
      rw [dif_pos hb, hg hb]

