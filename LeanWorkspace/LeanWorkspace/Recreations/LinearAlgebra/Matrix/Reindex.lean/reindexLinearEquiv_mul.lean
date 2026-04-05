import Mathlib

variable {l m n o : Type*} {l' m' n' o' : Type*} {m'' n'' : Type*}

variable (R A : Type*)

variable [Semiring R] [Semiring A] [Module R A]

theorem reindexLinearEquiv_mul [Fintype n] [Fintype n'] (eₘ : m ≃ m') (eₙ : n ≃ n') (eₒ : o ≃ o')
    (M : Matrix m n A) (N : Matrix n o A) :
    Matrix.reindexLinearEquiv R A eₘ eₙ M * Matrix.reindexLinearEquiv R A eₙ eₒ N =
      Matrix.reindexLinearEquiv R A eₘ eₒ (M * N) := submatrix_mul_equiv M N _ _ _

