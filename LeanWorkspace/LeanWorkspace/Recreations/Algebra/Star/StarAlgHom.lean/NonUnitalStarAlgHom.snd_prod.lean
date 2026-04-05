import Mathlib

variable (R A B C : Type*) [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
  [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B] [NonUnitalNonAssocSemiring C]
  [DistribMulAction R C] [Star C]

theorem snd_prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : (NonUnitalStarAlgHom.snd R B C).comp (NonUnitalStarAlgHom.prod f g) = g := by
  ext; rfl

