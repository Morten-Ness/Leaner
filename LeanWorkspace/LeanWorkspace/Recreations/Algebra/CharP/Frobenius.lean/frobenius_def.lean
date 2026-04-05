import Mathlib

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem frobenius_def : frobenius R p x = x ^ p := rfl

