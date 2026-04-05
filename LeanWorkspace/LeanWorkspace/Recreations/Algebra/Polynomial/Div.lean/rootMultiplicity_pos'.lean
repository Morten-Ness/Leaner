import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem rootMultiplicity_pos' {p : R[X]} {x : R} :
    0 < Polynomial.rootMultiplicity x p ↔ p ≠ 0 ∧ IsRoot p x := by
  rw [pos_iff_ne_zero, Ne, Polynomial.rootMultiplicity_eq_zero_iff, Classical.not_imp, and_comm]

