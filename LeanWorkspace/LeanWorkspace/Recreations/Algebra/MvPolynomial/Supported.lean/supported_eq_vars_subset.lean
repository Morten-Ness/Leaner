import Mathlib

variable {σ : Type*} {R : Type u}

variable [CommSemiring R] {p : MvPolynomial σ R}

variable {s t : Set σ}

theorem supported_eq_vars_subset : (MvPolynomial.supported R s : Set (MvPolynomial σ R)) = { p | ↑p.vars ⊆ s } := Set.ext fun _ ↦ MvPolynomial.mem_supported

