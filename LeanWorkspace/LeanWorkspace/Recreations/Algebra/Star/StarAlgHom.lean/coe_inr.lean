import Mathlib

variable (R A B C : Type*) [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
  [StarAddMonoid A] [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [StarAddMonoid B]
  [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [StarAddMonoid C]

theorem coe_inr : (NonUnitalStarAlgHom.inr R A B : B → A × B) = Prod.mk 0 := rfl

