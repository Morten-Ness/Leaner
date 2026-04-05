import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem ofFinsupp_eq_one {a} : (⟨a⟩ : R[X]) = 1 ↔ a = 1 := by rw [← Polynomial.ofFinsupp_one, Polynomial.ofFinsupp_inj]

