import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

theorem coe_centralizer (s : Set A) : (NonUnitalSubalgebra.centralizer R s : Set A) = s.centralizer := rfl

