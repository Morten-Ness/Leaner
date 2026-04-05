import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_smul [SMulZeroClass S R] (r : S) (p : R[X]) (n : ℕ) :
    coeff (r • p) n = r • coeff p n := by
  rfl

