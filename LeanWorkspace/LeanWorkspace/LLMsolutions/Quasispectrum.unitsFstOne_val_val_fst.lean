import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

theorem unitsFstOne_val_val_fst (x : (Unitization.unitsFstOne R A)) : x.val.val.fst = 1 := by
  exact x.property
