import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

theorem span_eq_toSubmodule (s : NonUnitalSubalgebra R A) :
    Submodule.span R (s : Set A) = s.toSubmodule := by
  simp [SetLike.ext'_iff, Submodule.coe_span_eq_self]

