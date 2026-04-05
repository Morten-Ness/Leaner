import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem nextCoeff_mul (hp : Polynomial.Monic p) (hq : Polynomial.Monic q) :
    nextCoeff (p * q) = nextCoeff p + nextCoeff q := by
  nontriviality
  simp only [← coeff_one_reverse]
  rw [reverse_mul] <;> simp [hp.leadingCoeff, hq.leadingCoeff, mul_coeff_one, add_comm]

