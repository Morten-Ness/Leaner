import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

theorem divp_sub_divp [CommRing α] (a b : α) (u₁ u₂ : αˣ) :
    a /ₚ u₁ - b /ₚ u₂ = (a * u₂ - u₁ * b) /ₚ (u₁ * u₂) := by
  simp only [sub_eq_add_neg, Units.neg_divp, Units.divp_add_divp, mul_neg]

