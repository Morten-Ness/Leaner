import Mathlib

variable {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p] (x y : R)

theorem frobenius_neg : frobenius R p (-x) = -frobenius R p x := map_neg ..

