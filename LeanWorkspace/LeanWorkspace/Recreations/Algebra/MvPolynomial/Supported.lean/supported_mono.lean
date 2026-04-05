import Mathlib

variable {σ : Type*} {R : Type u}

variable [CommSemiring R] {p : MvPolynomial σ R}

variable {s t : Set σ}

theorem supported_mono (st : s ⊆ t) : MvPolynomial.supported R s ≤ MvPolynomial.supported R t := Algebra.adjoin_mono (Set.image_mono st)

