import Mathlib

variable {σ : Type*} {R : Type u}

variable [CommSemiring R] {p : MvPolynomial σ R}

variable {s t : Set σ}

theorem supported_le_supported_iff [Nontrivial R] : MvPolynomial.supported R s ≤ MvPolynomial.supported R t ↔ s ⊆ t := by
  constructor
  · intro h i
    simpa using @h (X i)
  · exact MvPolynomial.supported_mono

