import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

variable [DecompositionMonoid α]

theorem IsRelPrime.mul_left_iff : IsRelPrime (x * y) z ↔ IsRelPrime x z ∧ IsRelPrime y z := ⟨fun H ↦ ⟨H.of_mul_left_left, H.of_mul_left_right⟩, fun ⟨H1, H2⟩ ↦ H1.mul_left H2⟩

