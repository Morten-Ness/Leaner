import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem pow_rootMultiplicity_not_dvd (p0 : p ≠ 0) (a : R) :
    ¬(Polynomial.X - Polynomial.C a) ^ (Polynomial.rootMultiplicity a p + 1) ∣ p := by rw [← Polynomial.rootMultiplicity_le_iff p0]

