import Mathlib

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem RingHom.iterate_map_frobenius (f : R →+* R) (p : ℕ) [ExpChar R p] (n : ℕ) :
    f^[n] (frobenius R p x) = frobenius R p (f^[n] x) := iterate_map_pow f _ _ _

