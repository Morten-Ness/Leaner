import Mathlib

variable {σ : Type*} {τ : Type*}

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (f : σ → MvPolynomial τ R)

theorem map_comp_C (f : R →+* S) : (map f).comp (C : R →+* MvPolynomial σ R) = C.comp f := by
  ext1
  apply map_C

-- mixing the two monad structures

