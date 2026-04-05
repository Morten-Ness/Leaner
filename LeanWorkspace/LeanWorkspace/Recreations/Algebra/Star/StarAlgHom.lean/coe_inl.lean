import Mathlib

variable (R A B C : Type*) [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
  [StarAddMonoid A] [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [StarAddMonoid B]
  [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [StarAddMonoid C]

theorem coe_inl : (NonUnitalStarAlgHom.inl R A B : A → A × B) = fun x => (x, 0) := rfl

