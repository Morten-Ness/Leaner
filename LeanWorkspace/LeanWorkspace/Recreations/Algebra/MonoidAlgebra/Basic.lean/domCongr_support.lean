import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

theorem domCongr_support (e : M ≃* N) (f : A[M]) : (MonoidAlgebra.domCongr R A e f).support = f.support.map e := by
  ext; simp

