import Mathlib

variable {M : Type*} [MulOneClass M] {s s₁ s₂ : Submonoid M}
  (h : s.MulSaturated) (h₁ : s₁.MulSaturated) (h₂ : s₂.MulSaturated)

theorem of_left {M : Type*} [CommMonoid M] {s : Submonoid M}
    (h : ∀ ⦃x y⦄, x * y ∈ s → x ∈ s) : s.MulSaturated := fun x y hxy ↦ ⟨h hxy, h <| mul_comm x y ▸ hxy⟩

