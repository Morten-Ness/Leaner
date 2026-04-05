import Mathlib

variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

theorem IsUnit.not_isPrimePow {n : R} (h : IsUnit n) : ¬IsPrimePow n := fun h' => h'.not_unit h

