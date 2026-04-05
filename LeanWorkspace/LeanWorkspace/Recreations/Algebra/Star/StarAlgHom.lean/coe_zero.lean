import Mathlib

variable {R A B C D : Type*} [Monoid R]

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [StarAddMonoid A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [StarAddMonoid B]

theorem coe_zero : ((0 : A →⋆ₙₐ[R] B) : A → B) = 0 := rfl

