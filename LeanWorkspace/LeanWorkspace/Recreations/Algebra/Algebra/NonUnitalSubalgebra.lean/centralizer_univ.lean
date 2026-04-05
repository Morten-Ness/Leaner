import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

theorem centralizer_univ : NonUnitalSubalgebra.centralizer R Set.univ = NonUnitalSubalgebra.center R A := SetLike.ext' (Set.centralizer_univ A)

