import Mathlib

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem iterateFrobenius_zero : iterateFrobenius R p 0 = RingHom.id R := RingHom.ext (iterateFrobenius_zero_apply R p)

