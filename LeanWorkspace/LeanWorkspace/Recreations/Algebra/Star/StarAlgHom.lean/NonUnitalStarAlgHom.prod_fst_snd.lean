import Mathlib

variable (R A B C : Type*) [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
  [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B] [NonUnitalNonAssocSemiring C]
  [DistribMulAction R C] [Star C]

theorem prod_fst_snd : NonUnitalStarAlgHom.prod (NonUnitalStarAlgHom.fst R A B) (NonUnitalStarAlgHom.snd R A B) = 1 := DFunLike.coe_injective Pi.prod_fst_snd

