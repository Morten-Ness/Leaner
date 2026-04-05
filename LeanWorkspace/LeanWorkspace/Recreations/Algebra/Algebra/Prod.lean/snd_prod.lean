import Mathlib

variable {R A B C : Type*}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

theorem snd_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : (AlgHom.snd R B C).comp (AlgHom.prod f g) = g := by ext; rfl

