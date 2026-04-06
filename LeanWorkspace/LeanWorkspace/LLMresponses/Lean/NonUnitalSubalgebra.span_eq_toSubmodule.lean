import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

theorem span_eq_toSubmodule (s : NonUnitalSubalgebra R A) :
    Submodule.span R (s : Set A) = s.toSubmodule := by
  ext x
  constructor
  · intro hx
    exact Submodule.span_le.2 (by
      intro y hy
      exact hy) hx
  · intro hx
    exact Submodule.subset_span hx
