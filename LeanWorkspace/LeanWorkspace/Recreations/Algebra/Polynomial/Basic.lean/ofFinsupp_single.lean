import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem ofFinsupp_single (n : ℕ) (r : R) : ⟨.single n r⟩ = Polynomial.monomial n r := by simp [Polynomial.monomial]

