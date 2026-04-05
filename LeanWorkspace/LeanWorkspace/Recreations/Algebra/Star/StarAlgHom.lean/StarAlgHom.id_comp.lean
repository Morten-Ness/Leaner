import Mathlib

variable {F R A B C D : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B]
  [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C] [Semiring D] [Algebra R D] [Star D]

theorem id_comp (f : A →⋆ₐ[R] B) : (StarAlgHom.id _ _).comp f = f := StarAlgHom.ext fun _ => rfl

