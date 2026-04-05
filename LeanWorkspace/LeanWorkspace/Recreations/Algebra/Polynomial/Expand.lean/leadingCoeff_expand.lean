import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem leadingCoeff_expand {p : ℕ} {f : R[X]} (hp : 0 < p) :
    (Polynomial.expand R p f).leadingCoeff = f.leadingCoeff := by
  simp_rw [leadingCoeff, Polynomial.natDegree_expand, Polynomial.coeff_expand_mul hp]

