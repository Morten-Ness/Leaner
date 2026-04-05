import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_natDegree : coeff p (Polynomial.natDegree p) = Polynomial.leadingCoeff p := rfl

