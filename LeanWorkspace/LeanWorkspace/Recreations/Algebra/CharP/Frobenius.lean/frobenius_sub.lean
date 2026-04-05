import Mathlib

variable {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p] (x y : R)

theorem frobenius_sub : frobenius R p (x - y) = frobenius R p x - frobenius R p y := map_sub ..

