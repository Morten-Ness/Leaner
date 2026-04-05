import Mathlib

variable {R : Type*} [CommRing R]

theorem homogenize_sub (p q : R[X]) (n : ℕ) :
    (p - q).homogenize n = p.homogenize n - q.homogenize n := map_sub (Polynomial.homogenizeLM n) p q

