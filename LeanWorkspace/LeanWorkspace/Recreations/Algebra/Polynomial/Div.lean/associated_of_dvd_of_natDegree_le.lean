import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

variable [IsDomain R]

theorem associated_of_dvd_of_natDegree_le {K} [Field K] {p q : K[X]} (hpq : p ∣ q) (hq : q ≠ 0)
    (h₁ : q.natDegree ≤ p.natDegree) : Associated p q := Polynomial.associated_of_dvd_of_natDegree_le_of_leadingCoeff hpq h₁
    (IsUnit.dvd (by rwa [← leadingCoeff_ne_zero, ← isUnit_iff_ne_zero] at hq))

