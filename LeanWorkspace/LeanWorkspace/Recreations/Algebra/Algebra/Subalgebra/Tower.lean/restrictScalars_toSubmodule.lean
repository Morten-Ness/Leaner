import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable {S A B} [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra S A] [Algebra R A] [Algebra S B] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

theorem restrictScalars_toSubmodule {U : Subalgebra S A} :
    Subalgebra.toSubmodule (U.restrictScalars R) = U.toSubmodule.restrictScalars R := SetLike.coe_injective rfl

