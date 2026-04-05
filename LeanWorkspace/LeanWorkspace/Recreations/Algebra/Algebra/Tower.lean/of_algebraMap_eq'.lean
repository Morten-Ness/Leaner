import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra S A] [Algebra S B]

theorem of_algebraMap_eq' [Algebra R A]
    (h : algebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq <| RingHom.ext_iff.1 h

