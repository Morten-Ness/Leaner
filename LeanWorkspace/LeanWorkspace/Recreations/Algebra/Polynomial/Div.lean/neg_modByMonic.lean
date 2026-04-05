import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem neg_modByMonic (p q : R[X]) : (-p) %ₘ q = -(p %ₘ q) := by
  rw [eq_neg_iff_add_eq_zero, ← Polynomial.add_modByMonic, neg_add_cancel, Polynomial.zero_modByMonic]

