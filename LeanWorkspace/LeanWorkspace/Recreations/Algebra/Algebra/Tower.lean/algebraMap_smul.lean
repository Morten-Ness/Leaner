import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [Semiring A] [Algebra R A]

variable [MulAction A M]

theorem algebraMap_smul [SMul R M] [IsScalarTower R A M] (r : R) (x : M) :
    algebraMap R A r • x = r • x := by
  rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]

