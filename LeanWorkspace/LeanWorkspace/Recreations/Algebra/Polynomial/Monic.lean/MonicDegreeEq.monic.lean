import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

theorem MonicDegreeEq.monic (p : MonicDegreeEq R n) :
    p.1.Monic := by
  nontriviality R
  rw [Polynomial.Monic, leadingCoeff, p.natDegree, p.2.1]

