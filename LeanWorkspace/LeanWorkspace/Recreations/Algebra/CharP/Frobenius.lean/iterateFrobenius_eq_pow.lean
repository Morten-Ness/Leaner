import Mathlib

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem iterateFrobenius_eq_pow : iterateFrobenius R p n = frobenius R p ^ n := by
  ext; simp [iterateFrobenius_def, iterate_frobenius]

