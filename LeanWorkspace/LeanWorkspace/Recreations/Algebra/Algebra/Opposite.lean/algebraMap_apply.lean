import Mathlib

variable {R S A B : Type*}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S A] [SMulCommClass R S A]

variable [IsScalarTower R S A]

theorem algebraMap_apply (c : R) : algebraMap R Aᵐᵒᵖ c = op (algebraMap R A c) := rfl

