import Mathlib

variable {σ : Type*} {R : Type u}

variable [CommSemiring R] {p : MvPolynomial σ R}

variable {s t : Set σ}

theorem X_mem_supported [Nontrivial R] {i : σ} : X i ∈ MvPolynomial.supported R s ↔ i ∈ s := by
  simp [MvPolynomial.mem_supported]

