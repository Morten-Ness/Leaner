import Mathlib

variable (R A : Type*) [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

set_option backward.isDefEq.respectTransparency false in
theorem center_eq_top (A : Type*) [NonUnitalCommSemiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] : NonUnitalSubalgebra.center R A = ⊤ := by
  ext x
  constructor
  · intro hx
    trivial
  · intro hx
    simp [NonUnitalSubalgebra.mem_center_iff]
