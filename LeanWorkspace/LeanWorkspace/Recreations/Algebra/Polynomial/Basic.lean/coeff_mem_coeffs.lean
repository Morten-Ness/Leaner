import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_mem_coeffs {p : R[X]} {n : ℕ} (h : p.coeff n ≠ 0) : p.coeff n ∈ p.coeffs := by
  classical
  simp only [Polynomial.coeffs, Polynomial.mem_support_iff, Finset.mem_image, Ne]
  exact ⟨n, h, rfl⟩

