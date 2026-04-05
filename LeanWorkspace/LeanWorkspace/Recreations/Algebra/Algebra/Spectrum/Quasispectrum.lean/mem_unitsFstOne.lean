import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

theorem mem_unitsFstOne {x : (Unitization R A)ˣ} : x ∈ Unitization.unitsFstOne R A ↔ x.val.fst = 1 := Iff.rfl

