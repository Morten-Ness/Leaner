import Mathlib

variable {R : Type*} [CommRing R]

theorem homogenize_neg (p : R[X]) (n : ℕ) : (-p).homogenize n = -p.homogenize n := map_neg (Polynomial.homogenizeLM n) p

