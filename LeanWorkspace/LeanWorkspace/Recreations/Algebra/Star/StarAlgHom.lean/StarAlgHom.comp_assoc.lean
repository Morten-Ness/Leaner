import Mathlib

variable {F R A B C D : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B]
  [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C] [Semiring D] [Algebra R D] [Star D]

theorem comp_assoc (f : C →⋆ₐ[R] D) (g : B →⋆ₐ[R] C) (h : A →⋆ₐ[R] B) :
    (f.comp g).comp h = f.comp (g.comp h) := rfl

