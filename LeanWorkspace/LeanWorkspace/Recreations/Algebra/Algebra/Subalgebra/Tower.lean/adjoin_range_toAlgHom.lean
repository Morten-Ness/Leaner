import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [CommSemiring S] [CommSemiring A]

variable [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

theorem adjoin_range_toAlgHom (t : Set A) :
    (Algebra.adjoin (toAlgHom R S A).range t).restrictScalars R =
      (Algebra.adjoin S t).restrictScalars R := Subalgebra.ext fun z ↦
    show z ∈ Subsemiring.closure (Set.range (algebraMap (toAlgHom R S A).range A) ∪ t : Set A) ↔
         z ∈ Subsemiring.closure (Set.range (algebraMap S A) ∪ t : Set A) by simp

