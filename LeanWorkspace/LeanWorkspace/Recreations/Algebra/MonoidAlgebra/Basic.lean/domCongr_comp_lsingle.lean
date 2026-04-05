import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

theorem domCongr_comp_lsingle (e : M ≃* N) (m : M) :
    (MonoidAlgebra.domCongr R A e).toLinearMap ∘ₗ lsingle m = lsingle (e m) := by ext; simp

