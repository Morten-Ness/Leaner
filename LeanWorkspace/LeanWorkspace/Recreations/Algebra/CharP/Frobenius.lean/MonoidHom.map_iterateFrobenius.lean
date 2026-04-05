import Mathlib

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem MonoidHom.map_iterateFrobenius (n : ℕ) :
    f (iterateFrobenius R p n x) = iterateFrobenius S p n (f x) := by
  simp [iterateFrobenius_def]

