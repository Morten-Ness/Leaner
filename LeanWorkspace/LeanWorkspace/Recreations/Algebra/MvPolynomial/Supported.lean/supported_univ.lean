import Mathlib

variable {σ : Type*} {R : Type u}

variable [CommSemiring R] {p : MvPolynomial σ R}

variable {s t : Set σ}

theorem supported_univ : MvPolynomial.supported R (Set.univ : Set σ) = ⊤ := by
  simp [Algebra.eq_top_iff, MvPolynomial.mem_supported]

