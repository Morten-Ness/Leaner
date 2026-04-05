import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem mem_coeffs_iff {p : R[X]} {c : R} : c ∈ p.coeffs ↔ ∃ n ∈ p.support, c = p.coeff n := by
  simp [Polynomial.coeffs, eq_comm, (Finset.mem_image)]

