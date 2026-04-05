import Mathlib

variable {R A B : Type*}

variable [CommSemiring R] [NonUnitalSemiring A] [NonUnitalSemiring B] [Module R B] [Module R A]

variable [SMulCommClass R A A] [IsScalarTower R A A]

variable [SMulCommClass R B B] [IsScalarTower R B B]

theorem commute_mulLeft_right (a b : A) : Commute (mulLeft R a) (mulRight R b) := by
  ext c
  exact (mul_assoc a c b).symm

