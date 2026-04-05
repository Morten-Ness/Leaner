import Mathlib

variable {l m n o : Type*} {l' m' n' o' : Type*} {m'' n'' : Type*}

variable (R A : Type*)

variable [Semiring R] [AddCommMonoid A] [Module R A]

theorem reindexLinearEquiv_symm (eₘ : m ≃ m') (eₙ : n ≃ n') :
    (Matrix.reindexLinearEquiv R A eₘ eₙ).symm = Matrix.reindexLinearEquiv R A eₘ.symm eₙ.symm := rfl

