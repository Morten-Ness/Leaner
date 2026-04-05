import Mathlib

variable {l m n o : Type*} {l' m' n' o' : Type*} {m'' n'' : Type*}

variable (R A : Type*)

variable [Semiring R] [AddCommMonoid A] [Module R A]

theorem reindexLinearEquiv_comp_apply (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'')
    (M : Matrix m n A) :
    (Matrix.reindexLinearEquiv R A e₁' e₂') (Matrix.reindexLinearEquiv R A e₁ e₂ M) =
      Matrix.reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') M := submatrix_submatrix _ _ _ _ _

