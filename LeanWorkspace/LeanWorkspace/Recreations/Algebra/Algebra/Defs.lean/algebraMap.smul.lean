import Mathlib

variable {A B : Type*} (a : A) (b : B) (C : Type*)
  [SMul A B] [CommSemiring B] [Semiring C] [Algebra B C]

theorem algebraMap.smul [SMul A C] [IsScalarTower A B C] :
    algebraMap B C (a • b) = a • (algebraMap B C b) := coe_smul _ _ _

