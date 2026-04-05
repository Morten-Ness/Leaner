import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

theorem rootMultiplicity_mul' {p q : R[X]} {x : R}
    (hpq : (p /ₘ (Polynomial.X - Polynomial.C x) ^ p.rootMultiplicity x).eval x *
      (q /ₘ (Polynomial.X - Polynomial.C x) ^ q.rootMultiplicity x).eval x ≠ 0) :
    rootMultiplicity x (p * q) = rootMultiplicity x p + rootMultiplicity x q := by
  simp_rw [eval_divByMonic_eq_trailingCoeff_comp] at hpq
  simp_rw [Polynomial.rootMultiplicity_eq_natTrailingDegree, mul_comp, natTrailingDegree_mul' hpq]

