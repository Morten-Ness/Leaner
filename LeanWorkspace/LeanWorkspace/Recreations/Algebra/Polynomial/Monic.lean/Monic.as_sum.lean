import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem Monic.as_sum (hp : p.Monic) :
    p = Polynomial.X ^ p.natDegree + ∑ i ∈ range p.natDegree, Polynomial.C (p.coeff i) * Polynomial.X ^ i := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow, sum_range_succ_comm]
  suffices Polynomial.C (p.coeff p.natDegree) = 1 by rw [this, one_mul]
  exact congr_arg Polynomial.C hp

