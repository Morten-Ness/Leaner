import Mathlib

variable {M : Type*} [MulOneClass M] {s s₁ s₂ : Submonoid M}
  (h : s.MulSaturated) (h₁ : s₁.MulSaturated) (h₂ : s₂.MulSaturated)

theorem of_right {M : Type*} [CommMonoid M] {s : Submonoid M}
    (h : ∀ ⦃x y⦄, x * y ∈ s → y ∈ s) : s.MulSaturated := by
  intro a b hab
  constructor
  · have h' : b * a ∈ s := by simpa [mul_comm] using hab
    simpa [mul_comm] using (h h')
  · exact h hab
