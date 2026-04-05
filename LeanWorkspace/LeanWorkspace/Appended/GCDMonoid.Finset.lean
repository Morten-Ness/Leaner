import Mathlib

section

variable {ι α β γ : Type*}

variable {s : Finset ι}

theorem Int.finsetGcd_nonneg {f : ι → ℤ} : 0 ≤ s.gcd f := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s has ih =>
    rw [Finset.gcd_cons, ← Int.coe_gcd]
    grind

end

section

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) :
    s₁.gcd f = s₂.gcd g := by
  subst hs
  exact Finset.fold_congr hfg

end

section

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

variable [Div α] [MulDivCancelClass α] {f : ι → α} {s : Finset ι} {i : ι}

theorem gcd_div_eq_one (his : i ∈ s) (hfi : f i ≠ 0) : s.gcd (fun j ↦ f j / s.gcd f) = 1 := by
  obtain ⟨g, he, hg⟩ := Finset.extract_gcd f ⟨i, his⟩
  refine (Finset.gcd_congr rfl fun a ha ↦ ?_).trans hg
  rw [he a ha, mul_div_cancel_left₀]
  exact mt Finset.gcd_eq_zero_iff.1 fun h ↦ hfi <| h i his

end

section

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_image [DecidableEq β] {g : γ → β} (s : Finset γ) :
    (s.image g).gcd f = s.gcd (f ∘ g) := by
  classical induction s using Finset.induction <;> simp [*]

end

section

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_mono (h : s₁ ⊆ s₂) : s₂.gcd f ∣ s₁.gcd f := Finset.dvd_gcd fun _ hb ↦ Finset.gcd_dvd (h hb)

end

section

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ∣ g b) : s.gcd f ∣ s.gcd g := Finset.dvd_gcd fun b hb ↦ (Finset.gcd_dvd hb).trans (h b hb)

end

section

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem lcm_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) :
    s₁.lcm f = s₂.lcm g := by
  subst hs
  exact Finset.fold_congr hfg

end

section

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem lcm_image [DecidableEq β] {g : γ → β} (s : Finset γ) :
    (s.image g).lcm f = s.lcm (f ∘ g) := by
  classical induction s using Finset.induction <;> simp [*]

end

section

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem lcm_mono (h : s₁ ⊆ s₂) : s₁.lcm f ∣ s₂.lcm f := Finset.lcm_dvd fun _ hb ↦ Finset.dvd_lcm (h hb)

end

section

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem lcm_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ∣ g b) : s.lcm f ∣ s.lcm g := Finset.lcm_dvd fun b hb ↦ (h b hb).trans (Finset.dvd_lcm hb)

end
