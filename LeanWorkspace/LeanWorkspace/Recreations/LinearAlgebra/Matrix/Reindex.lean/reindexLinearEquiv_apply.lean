import Mathlib

variable {l m n o : Type*} {l' m' n' o' : Type*} {m'' n'' : Type*}

variable (R A : Type*)

variable [Semiring R] [AddCommMonoid A] [Module R A]

theorem reindexLinearEquiv_apply (eₘ : m ≃ m') (eₙ : n ≃ n') (M : Matrix m n A) :
    Matrix.reindexLinearEquiv R A eₘ eₙ M = reindex eₘ eₙ M := rfl

