import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem X_mul : Polynomial.X * p = p * Polynomial.X := by
  rcases p with ⟨⟩
  simp only [Polynomial.X, ← Polynomial.ofFinsupp_single, ← Polynomial.ofFinsupp_mul, ofFinsupp.injEq]
  ext
  simp [AddMonoidAlgebra.mul_apply, add_comm]

