import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Nontrivial R]

variable [Semiring R]

theorem natDegree_X_pow_add_C {n : ℕ} {r : R} : (Polynomial.X ^ n + Polynomial.C r).natDegree = n := by
  simp

