import Mathlib

variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

theorem not_isPrimePow_one : ¬IsPrimePow (1 : R) := isUnit_one.not_isPrimePow

