import Mathlib

variable {R A B C D : Type*} [Monoid R]

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [Star C]

variable [NonUnitalNonAssocSemiring D] [DistribMulAction R D] [Star D]

theorem comp_apply (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) (a : A) : NonUnitalStarAlgHom.comp f g a = f (g a) := rfl

