import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem Monic.add_of_right (hq : Polynomial.Monic q) (hpq : degree p < degree q) : Polynomial.Monic (p + q) := by
  rwa [Polynomial.Monic, Polynomial.leadingCoeff_add_of_degree_lt hpq]

