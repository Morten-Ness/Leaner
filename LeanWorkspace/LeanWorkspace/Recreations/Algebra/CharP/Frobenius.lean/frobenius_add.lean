import Mathlib

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem frobenius_add : frobenius R p (x + y) = frobenius R p x + frobenius R p y := (frobenius R p).map_add x y

