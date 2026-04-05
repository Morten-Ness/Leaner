import Mathlib

variable {l m n o : Type*} {l' m' n' o' : Type*} {m'' n'' : Type*}

variable (R A : Type*)

variable [Semiring R] [AddCommMonoid A] [Module R A]

theorem reindexLinearEquiv_trans (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'') :
    (Matrix.reindexLinearEquiv R A e₁ e₂).trans (Matrix.reindexLinearEquiv R A e₁' e₂') =
      (Matrix.reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') : _ ≃ₗ[R] _) := by
  ext
  rfl

