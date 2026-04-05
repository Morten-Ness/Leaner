import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

theorem domCongr_refl : MonoidAlgebra.domCongr R A (.refl M) = .refl := by ext; simp

