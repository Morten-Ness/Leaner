import Mathlib

variable {σ : Type*} {R : Type u}

variable [CommSemiring R] {p : MvPolynomial σ R}

theorem supported_eq_range_rename (s : Set σ) : MvPolynomial.supported R s = (rename ((↑) : s → σ)).range := by
  rw [MvPolynomial.supported, Set.image_eq_range, adjoin_range_eq_range_aeval, rename]
  congr

