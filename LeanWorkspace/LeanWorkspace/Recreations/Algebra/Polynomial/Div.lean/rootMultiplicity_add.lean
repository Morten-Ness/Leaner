import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem rootMultiplicity_add {p q : R[X]} (a : R) (hzero : p + q ≠ 0) :
    min (Polynomial.rootMultiplicity a p) (Polynomial.rootMultiplicity a q) ≤ Polynomial.rootMultiplicity a (p + q) := by
  rw [Polynomial.le_rootMultiplicity_iff hzero]
  exact min_pow_dvd_add (Polynomial.pow_rootMultiplicity_dvd p a) (Polynomial.pow_rootMultiplicity_dvd q a)

