import Mathlib

variable {F R A B C D : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B]
  [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C] [Semiring D] [Algebra R D] [Star D]

theorem comp_id (f : A →⋆ₐ[R] B) : f.comp (StarAlgHom.id _ _) = f := StarAlgHom.ext fun _ => rfl

