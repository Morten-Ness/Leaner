import Mathlib

variable {F R A B C D : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B]
  [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C] [Semiring D] [Algebra R D] [Star D]

theorem coe_comp (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) : ⇑(StarAlgHom.comp f g) = f ∘ g := rfl

