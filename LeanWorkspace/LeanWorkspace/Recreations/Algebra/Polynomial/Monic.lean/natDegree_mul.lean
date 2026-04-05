import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_mul (hp : p.Monic) (hq : q.Monic) :
    (p * q).natDegree = p.natDegree + q.natDegree := by
  nontriviality R
  apply natDegree_mul'
  simp [hp.leadingCoeff, hq.leadingCoeff]

