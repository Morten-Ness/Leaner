import Mathlib

variable (R A : Type*) [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

theorem mem_center_iff {a : A} : a ∈ NonUnitalSubalgebra.center R A ↔ ∀ b : A, b * a = a * b := Subsemigroup.mem_center_iff

