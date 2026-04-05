import Mathlib

variable {R : Type u} [CommRing R] {p n : ℕ} [ExpChar R p] {f : R[X]} {r : R}

theorem rootMultiplicity_expand :
    (Polynomial.expand R p f).rootMultiplicity r = p * f.rootMultiplicity (r ^ p) := by
  rw [← pow_one p, Polynomial.rootMultiplicity_expand_pow]

