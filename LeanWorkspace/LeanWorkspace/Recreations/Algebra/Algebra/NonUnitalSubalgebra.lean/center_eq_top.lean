import Mathlib

variable (R A : Type*) [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

set_option backward.isDefEq.respectTransparency false in
theorem center_eq_top (A : Type*) [NonUnitalCommSemiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : NonUnitalSubalgebra.center R A = ⊤ := SetLike.coe_injective (Set.center_eq_univ A)

