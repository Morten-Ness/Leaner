import Mathlib

variable {F R A B C D : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B]
  [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C] [Semiring D] [Algebra R D] [Star D]

theorem copy_eq (f : A →⋆ₐ[R] B) (f' : A → B) (h : f' = f) : f.copy f' h = f := DFunLike.ext' h

