import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem rootMultiplicity_eq_zero_iff {p : R[X]} {x : R} :
    Polynomial.rootMultiplicity x p = 0 ↔ IsRoot p x → p = 0 := by
  classical
  simp only [Polynomial.rootMultiplicity_eq_multiplicity, ite_eq_left_iff, multiplicity_eq_zero,
    Polynomial.dvd_iff_isRoot, not_imp_not]

