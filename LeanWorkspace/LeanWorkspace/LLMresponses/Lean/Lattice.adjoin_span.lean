FAIL
import Mathlib

universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B]
variable [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_span {s : Set A} :
    Algebra.adjoin R (Submodule.span R s : Set A) = Algebra.adjoin R s := by
  rw [Algebra.adjoin_eq_span, Algebra.adjoin_eq_span]
  congr
  ext x
  constructor
  · intro hx
    exact Submodule.span_mono
      (by
        intro y hy
        exact Submodule.subset_span (Algebra.subset_adjoin (Submodule.subset_span hy)))
      hx
  · intro hx
    exact Submodule.span_mono
      (by
        intro y hy
        exact Submodule.subset_span (Algebra.subset_adjoin hy))
      hx
