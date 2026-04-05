import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem support_erase (p : R[X]) (n : ℕ) : Polynomial.support (p.erase n) = (Polynomial.support p).erase n := by
  simp only [Polynomial.support, erase_def, Finsupp.support_erase, AddMonoidAlgebra.erase, ofCoeff,
    AddMonoidAlgebra.coeff]

