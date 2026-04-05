import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem le_rootMultiplicity_mul {p q : R[X]} (x : R) (hpq : p * q ≠ 0) :
    Polynomial.rootMultiplicity x p + Polynomial.rootMultiplicity x q ≤ Polynomial.rootMultiplicity x (p * q) := by
  rw [Polynomial.le_rootMultiplicity_iff hpq, pow_add]
  gcongr <;> apply Polynomial.pow_rootMultiplicity_dvd

