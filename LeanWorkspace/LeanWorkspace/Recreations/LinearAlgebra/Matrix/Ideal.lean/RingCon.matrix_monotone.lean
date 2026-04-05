import Mathlib

variable {R n : Type*}

variable [NonUnitalNonAssocSemiring R] [Fintype n]

theorem matrix_monotone : Monotone (RingCon.matrix (R := R) n) :=
  fun _ _ hc _ _ h _ _ ↦ hc (h _ _)

