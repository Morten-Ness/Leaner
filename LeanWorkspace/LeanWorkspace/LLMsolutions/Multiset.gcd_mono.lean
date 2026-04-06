import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem gcd_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₂.gcd ∣ s₁.gcd := by
  induction s₁ using Multiset.induction_on with
  | empty =>
      simp
  | @cons a s₁ ih =>
      have hs : s₁ ⊆ s₂ := fun x hx => h <| by simp [hx]
      have hdiv : s₂.gcd ∣ s₁.gcd := ih hs
      have ha_mem : a ∈ s₂ := h (by simp)
      have ha : s₂.gcd ∣ a := Multiset.gcd_dvd ha_mem
      simpa [Multiset.gcd_cons] using dvd_gcd ha hdiv
