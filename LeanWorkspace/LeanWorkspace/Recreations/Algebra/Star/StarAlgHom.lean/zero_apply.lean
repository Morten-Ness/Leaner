import Mathlib

variable {R A B C D : Type*} [Monoid R]

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [StarAddMonoid A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [StarAddMonoid B]

theorem zero_apply (a : A) : (0 : A →⋆ₙₐ[R] B) a = 0 := rfl

