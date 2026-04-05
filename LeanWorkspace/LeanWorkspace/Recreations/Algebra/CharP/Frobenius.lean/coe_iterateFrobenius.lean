import Mathlib

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem coe_iterateFrobenius : iterateFrobenius R p n = (frobenius R p)^[n] := (pow_iterate p n).symm

