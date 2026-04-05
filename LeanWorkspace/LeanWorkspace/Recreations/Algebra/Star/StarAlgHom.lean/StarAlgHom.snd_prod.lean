import Mathlib

variable (R A B C : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B]
  [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C]

theorem snd_prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : (StarAlgHom.snd R B C).comp (StarAlgHom.prod f g) = g := by
  ext; rfl

