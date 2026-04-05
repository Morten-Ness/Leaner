import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]} {a : R}

variable [NoZeroDivisors R]

theorem nextCoeff_C_mul : (Polynomial.C a * p).nextCoeff = a * p.nextCoeff := by
  by_cases h₀ : a = 0 <;> simp [h₀, nextCoeff, Polynomial.natDegree_C_mul]

