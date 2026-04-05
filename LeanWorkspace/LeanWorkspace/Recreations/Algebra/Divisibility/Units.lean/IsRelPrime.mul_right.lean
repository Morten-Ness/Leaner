import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

variable [DecompositionMonoid α]

theorem IsRelPrime.mul_right (H1 : IsRelPrime x y) (H2 : IsRelPrime x z) :
    IsRelPrime x (y * z) := by
  rw [isRelPrime_comm] at H1 H2 ⊢; exact H1.mul_left H2

