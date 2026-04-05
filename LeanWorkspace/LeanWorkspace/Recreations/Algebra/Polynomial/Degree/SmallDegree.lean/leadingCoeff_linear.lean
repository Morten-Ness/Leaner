import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem leadingCoeff_linear (ha : a ≠ 0) : leadingCoeff (Polynomial.C a * Polynomial.X + Polynomial.C b) = a := by
  rw [add_comm, Polynomial.leadingCoeff_add_of_degree_lt (degree_C_lt_degree_C_mul_X ha),
    leadingCoeff_C_mul_X]

