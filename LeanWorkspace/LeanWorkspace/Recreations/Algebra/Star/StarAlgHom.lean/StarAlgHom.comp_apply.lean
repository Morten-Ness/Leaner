import Mathlib

variable {F R A B C D : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B]
  [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C] [Semiring D] [Algebra R D] [Star D]

theorem comp_apply (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) (a : A) : StarAlgHom.comp f g a = f (g a) := rfl

