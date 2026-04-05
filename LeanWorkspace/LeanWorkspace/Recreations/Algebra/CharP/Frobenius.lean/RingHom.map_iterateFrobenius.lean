import Mathlib

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem RingHom.map_iterateFrobenius (n : ℕ) :
    g (iterateFrobenius R p n x) = iterateFrobenius S p n (g x) := g.toMonoidHom.map_iterateFrobenius p x n

