import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [Semiring S] [AddCommMonoid A]

variable [Algebra R S] [Module S A] [Module R A] [IsScalarTower R S A]

theorem span_algebraMap_image_of_tower {S T : Type*} [CommSemiring S] [Semiring T] [Module R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] (a : Set S) :
    Submodule.span R (algebraMap S T '' a) =
      (Submodule.span R a).map ((Algebra.linearMap S T).restrictScalars R) := (Submodule.span_image <| (Algebra.linearMap S T).restrictScalars R).trans rfl

