import Mathlib

variable {σ : Type*} {R : Type u}

variable [CommSemiring R] {p : MvPolynomial σ R}

variable {s t : Set σ}

theorem supported_strictMono [Nontrivial R] :
    StrictMono (MvPolynomial.supported R : Set σ → Subalgebra R (MvPolynomial σ R)) := strictMono_of_le_iff_le fun _ _ ↦ MvPolynomial.supported_le_supported_iff.symm

