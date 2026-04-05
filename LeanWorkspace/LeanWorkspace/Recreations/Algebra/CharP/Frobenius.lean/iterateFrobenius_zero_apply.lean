import Mathlib

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem iterateFrobenius_zero_apply : iterateFrobenius R p 0 x = x := by
  rw [iterateFrobenius_def, pow_zero, pow_one]

