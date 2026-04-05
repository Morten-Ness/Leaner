import Mathlib

variable {R A B C D : Type*} [Monoid R]

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [Star C]

variable [NonUnitalNonAssocSemiring D] [DistribMulAction R D] [Star D]

theorem coe_one : ((1 : A →⋆ₙₐ[R] A) : A → A) = id := rfl

