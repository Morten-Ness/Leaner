import Mathlib

variable {l m n o : Type*} {l' m' n' o' : Type*} {m'' n'' : Type*}

variable (R A : Type*)

variable [Semiring R] [Semiring A] [Module R A]

theorem mul_reindexLinearEquiv_one [Fintype n] [DecidableEq o] (e₁ : o ≃ n) (e₂ : o ≃ n')
    (M : Matrix m n A) :
    M * (Matrix.reindexLinearEquiv R A e₁ e₂ 1) =
      Matrix.reindexLinearEquiv R A (Equiv.refl m) (e₁.symm.trans e₂) M := haveI := Fintype.ofEquiv _ e₁.symm
  mul_submatrix_one _ _ _

