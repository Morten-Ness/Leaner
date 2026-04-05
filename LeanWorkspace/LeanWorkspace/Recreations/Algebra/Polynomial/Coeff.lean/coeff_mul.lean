import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_mul (p q : R[X]) (n : ℕ) :
    coeff (p * q) n = ∑ x ∈ antidiagonal n, coeff p x.1 * coeff q x.2 := by
  rcases p with ⟨p⟩; rcases q with ⟨q⟩
  simp_rw [← ofFinsupp_mul, coeff]
  exact AddMonoidAlgebra.mul_apply_antidiagonal p q n _ Finset.mem_antidiagonal

