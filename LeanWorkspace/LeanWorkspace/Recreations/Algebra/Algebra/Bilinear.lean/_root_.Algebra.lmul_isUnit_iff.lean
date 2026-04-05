import Mathlib

variable {R A B : Type*}

variable [CommSemiring R] [Semiring A] [Algebra R A]

theorem _root_.Algebra.lmul_isUnit_iff {x : A} :
    IsUnit (Algebra.lmul R A x) ↔ IsUnit x := by
  rw [Module.End.isUnit_iff, Iff.comm]
  exact IsUnit.isUnit_iff_mulLeft_bijective

