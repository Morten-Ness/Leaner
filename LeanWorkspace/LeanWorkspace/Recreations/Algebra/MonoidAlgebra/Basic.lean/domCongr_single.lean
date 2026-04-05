import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

theorem domCongr_single (e : M ≃* N) (m : M) (a : A) :
    MonoidAlgebra.domCongr R A e (single m a) = single (e m) a := by simp [MonoidAlgebra.domCongr]

