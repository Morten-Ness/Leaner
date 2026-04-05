import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem ofFinsupp_eq_zero {a} : (⟨a⟩ : R[X]) = 0 ↔ a = 0 := by
  rw [← Polynomial.ofFinsupp_zero, Polynomial.ofFinsupp_inj]

