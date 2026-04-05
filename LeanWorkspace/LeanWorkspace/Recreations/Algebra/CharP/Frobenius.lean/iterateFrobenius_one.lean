import Mathlib

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem iterateFrobenius_one : iterateFrobenius R p 1 = frobenius R p := RingHom.ext (iterateFrobenius_one_apply R p)

