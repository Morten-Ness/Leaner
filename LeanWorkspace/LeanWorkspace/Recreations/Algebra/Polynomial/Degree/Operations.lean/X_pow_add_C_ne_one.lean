import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Nontrivial R]

variable [Semiring R]

theorem X_pow_add_C_ne_one {n : ℕ} (hn : 0 < n) (a : R) : (Polynomial.X : R[X]) ^ n + Polynomial.C a ≠ 1 := fun h =>
  hn.ne' <| by simpa only [Polynomial.natDegree_X_pow_add_C, natDegree_one] using congr_arg natDegree h

