import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [Semiring A] [Algebra R A]

variable [MulAction A M]

theorem of_algebraMap_smul [SMul R M] (h : ∀ (r : R) (x : M), algebraMap R A r • x = r • x) :
    IsScalarTower R A M where
  smul_assoc r a x := by rw [Algebra.smul_def, mul_smul, h]

