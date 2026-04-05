import Mathlib

variable (R A B C : Type*) [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
  [StarAddMonoid A] [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [StarAddMonoid B]
  [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [StarAddMonoid C]

theorem inr_apply (x : B) : NonUnitalStarAlgHom.inr R A B x = (0, x) := rfl

