import Mathlib

variable {R A B C D : Type*} [Monoid R]

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [Star C]

variable [NonUnitalNonAssocSemiring D] [DistribMulAction R D] [Star D]

theorem comp_assoc (f : C →⋆ₙₐ[R] D) (g : B →⋆ₙₐ[R] C) (h : A →⋆ₙₐ[R] B) :
    (f.comp g).comp h = f.comp (g.comp h) := rfl

