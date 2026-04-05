import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem support_update (p : R[X]) (n : ℕ) (a : R) [Decidable (a = 0)] :
    Polynomial.support (p.update n a) = if a = 0 then p.support.erase n else insert n p.support := by
  classical
    simp only [Polynomial.support, Function.update, Finsupp.support_update, AddMonoidAlgebra.update, ofCoeff,
      AddMonoidAlgebra.coeff]
    congr

