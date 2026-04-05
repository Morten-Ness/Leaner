import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

variable [DecompositionMonoid α]

theorem IsRelPrime.mul_right_iff : IsRelPrime x (y * z) ↔ IsRelPrime x y ∧ IsRelPrime x z := ⟨fun H ↦ ⟨H.of_mul_right_left, H.of_mul_right_right⟩, fun ⟨H1, H2⟩ ↦ H1.mul_right H2⟩

