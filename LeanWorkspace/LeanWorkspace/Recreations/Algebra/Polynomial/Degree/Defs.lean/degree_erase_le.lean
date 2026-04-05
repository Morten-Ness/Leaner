import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem degree_erase_le (p : R[X]) (n : ℕ) : Polynomial.degree (p.erase n) ≤ Polynomial.degree p := by
  simp only [erase_def, AddMonoidAlgebra.erase, AddMonoidAlgebra.coeff, AddMonoidAlgebra.ofCoeff,
    Polynomial.degree, support]
  apply sup_mono
  simpa using Finset.erase_subset ..

