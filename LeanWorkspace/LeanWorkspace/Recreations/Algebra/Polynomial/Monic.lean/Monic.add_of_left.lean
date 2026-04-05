import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem Monic.add_of_left (hp : Polynomial.Monic p) (hpq : degree q < degree p) : Polynomial.Monic (p + q) := by
  rwa [Polynomial.Monic, add_comm, Polynomial.leadingCoeff_add_of_degree_lt hpq]

