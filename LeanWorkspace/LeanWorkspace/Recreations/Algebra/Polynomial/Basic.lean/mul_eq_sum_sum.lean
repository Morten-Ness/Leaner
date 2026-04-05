import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem mul_eq_sum_sum :
    p * q = ∑ i ∈ p.support, q.sum fun j a => (Polynomial.monomial (i + j)) (p.coeff i * a) := by
  apply Polynomial.toFinsupp_injective
  simp_rw [Polynomial.sum, Polynomial.coeff, Polynomial.toFinsupp_sum, Polynomial.support, Polynomial.toFinsupp_mul, Polynomial.toFinsupp_monomial,
    AddMonoidAlgebra.mul_def, Finsupp.sum]

