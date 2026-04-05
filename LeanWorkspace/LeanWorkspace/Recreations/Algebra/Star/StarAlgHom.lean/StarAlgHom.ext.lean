import Mathlib

variable {F R A B C D : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B]
  [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C] [Semiring D] [Algebra R D] [Star D]

theorem ext {f g : A →⋆ₐ[R] B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

