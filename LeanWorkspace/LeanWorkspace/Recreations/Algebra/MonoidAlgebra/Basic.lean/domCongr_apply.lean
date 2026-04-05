import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

theorem domCongr_apply (e : M ≃* N) (x : A[M]) (n : N) : MonoidAlgebra.domCongr R A e x n = x (e.symm n) := by
  simp [MonoidAlgebra.domCongr]

