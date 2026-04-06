import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ∣ g b) : s.gcd f ∣ s.gcd g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      simp only [Finset.gcd_insert, ha]
      have h₁ : f a ∣ g a := h a (Finset.mem_insert_self a s)
      have h₂ : s.gcd f ∣ s.gcd g := by
        apply ih
        intro b hb
        exact h b (Finset.mem_insert_of_mem hb)
      exact gcd_dvd_gcd h₁ h₂
