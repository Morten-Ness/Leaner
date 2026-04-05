import Mathlib

open scoped Algebra

variable (R S A M : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [FaithfulSMul R A]

theorem Module.IsTorsionFree.of_faithfulSMul [Semiring S] [Module S R] [Module S A]
    [IsScalarTower S R A] [IsTorsionFree S A] : IsTorsionFree S R := (FaithfulSMul.algebraMap_injective R A).moduleIsTorsionFree _
    (by simp [Algebra.algebraMap_eq_smul_one])

