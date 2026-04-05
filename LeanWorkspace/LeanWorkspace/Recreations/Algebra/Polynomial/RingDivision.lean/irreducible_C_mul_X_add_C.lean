import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

variable [IsDomain R] {p q : R[X]}

theorem irreducible_C_mul_X_add_C {a b : R} (ha : a ≠ 0) (hab : IsRelPrime a b) :
    Irreducible (Polynomial.C a * Polynomial.X + Polynomial.C b) := by
  apply Polynomial.irreducible_of_degree_eq_one_of_isRelPrime_coeff
  · compute_degree!
  · simpa using hab.symm

