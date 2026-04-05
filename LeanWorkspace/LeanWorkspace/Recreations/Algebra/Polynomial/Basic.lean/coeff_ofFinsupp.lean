import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_ofFinsupp (p) : Polynomial.coeff (⟨p⟩ : R[X]) = p := by rw [Polynomial.coeff]

