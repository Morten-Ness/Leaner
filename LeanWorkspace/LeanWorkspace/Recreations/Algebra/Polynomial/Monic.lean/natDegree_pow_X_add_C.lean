import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_pow_X_add_C [Nontrivial R] (n : ℕ) (r : R) : ((Polynomial.X + Polynomial.C r) ^ n).natDegree = n := by
  rw [Polynomial.Monic.natDegree_pow (Polynomial.monic_X_add_C r), natDegree_X_add_C, mul_one]

