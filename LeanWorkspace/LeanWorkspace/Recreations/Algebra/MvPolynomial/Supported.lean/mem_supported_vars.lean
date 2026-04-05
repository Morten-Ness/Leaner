import Mathlib

variable {σ : Type*} {R : Type u}

variable [CommSemiring R] {p : MvPolynomial σ R}

variable {s t : Set σ}

theorem mem_supported_vars (p : MvPolynomial σ R) : p ∈ MvPolynomial.supported R (↑p.vars : Set σ) := by
  rw [MvPolynomial.mem_supported]

