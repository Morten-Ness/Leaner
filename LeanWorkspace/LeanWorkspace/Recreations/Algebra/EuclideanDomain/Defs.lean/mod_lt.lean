import Mathlib

variable {R : Type u} [EuclideanDomain R]

theorem mod_lt : ∀ (a) {b : R}, b ≠ 0 → a % b ≺ b := EuclideanDomain.remainder_lt

