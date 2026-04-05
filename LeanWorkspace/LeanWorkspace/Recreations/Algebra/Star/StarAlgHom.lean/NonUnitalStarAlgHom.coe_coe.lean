import Mathlib

variable {R A B C D : Type*} [Monoid R]

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [Star C]

variable [NonUnitalNonAssocSemiring D] [DistribMulAction R D] [Star D]

theorem coe_coe {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F R A B]
    [StarHomClass F A B] (f : F) :
    ⇑(f : A →⋆ₙₐ[R] B) = f := rfl

