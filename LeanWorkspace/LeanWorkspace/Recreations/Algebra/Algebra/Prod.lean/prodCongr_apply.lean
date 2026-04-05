import Mathlib

variable {R A B C : Type*}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable {S T A B : Type*} [Semiring A] [Semiring B]
  [Semiring S] [Semiring T] [Algebra R S] [Algebra R T] [Algebra R A] [Algebra R B]

variable (l : S ≃ₐ[R] A) (r : T ≃ₐ[R] B)

theorem prodCongr_apply (x : S × T) : AlgEquiv.prodCongr l r x = Equiv.prodCongr l r x := rfl

-- Priority `low` to ensure generic `map_{add, mul, zero, one}` lemmas are applied first

