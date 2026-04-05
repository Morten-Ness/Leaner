import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Nontrivial R]

variable [Semiring R]

theorem nextCoeff_X_add_C [Semiring S] (c : S) : nextCoeff (Polynomial.X + Polynomial.C c) = c := by
  nontriviality S
  simp [nextCoeff_of_natDegree_pos]

