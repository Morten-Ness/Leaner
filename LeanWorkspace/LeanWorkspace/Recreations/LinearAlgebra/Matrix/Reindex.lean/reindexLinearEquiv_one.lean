import Mathlib

variable {l m n o : Type*} {l' m' n' o' : Type*} {m'' n'' : Type*}

variable (R A : Type*)

variable [Semiring R] [AddCommMonoid A] [Module R A]

theorem reindexLinearEquiv_one [DecidableEq m] [DecidableEq m'] [One A] (e : m ≃ m') :
    Matrix.reindexLinearEquiv R A e e (1 : Matrix m m A) = 1 := submatrix_one_equiv e.symm

