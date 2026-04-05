import Mathlib

variable {A B : Type*} (a : A) (b : B) (C : Type*)
  [SMul A B] [CommSemiring B] [Semiring C] [Algebra B C]

theorem algebraMap.coe_smul [SMul A C] [IsScalarTower A B C] : (a • b : B) = a • (b : C) := by
  simp [Algebra.algebraMap_eq_smul_one]

