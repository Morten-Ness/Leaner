import Mathlib

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem RingHom.map_frobenius : g (frobenius R p x) = frobenius S p (g x) := map_pow g x p

