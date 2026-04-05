import Mathlib

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem iterateFrobenius_one_apply : iterateFrobenius R p 1 x = x ^ p := by
  rw [iterateFrobenius_def, pow_one]

