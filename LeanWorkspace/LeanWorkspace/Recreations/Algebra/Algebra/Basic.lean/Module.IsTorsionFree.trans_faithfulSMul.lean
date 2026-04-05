import Mathlib

open scoped Algebra

variable (R S A M : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [FaithfulSMul R A]

theorem Module.IsTorsionFree.trans_faithfulSMul [Nontrivial R] [IsCancelMulZero A] [AddCommMonoid M]
    [Module A M] [Module R M] [IsTorsionFree A M] [IsScalarTower R A M] : IsTorsionFree R M := .comap (algebraMap R A) (fun r hr ↦ .of_ne_zero <| by simpa using hr.ne_zero) (by simp)

-- see Note [lower instance priority]

