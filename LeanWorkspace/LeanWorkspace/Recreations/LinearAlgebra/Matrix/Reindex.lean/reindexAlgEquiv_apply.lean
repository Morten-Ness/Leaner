import Mathlib

variable {l m n o : Type*} {l' m' n' o' : Type*} {m'' n'' : Type*}

variable (R A : Type*)

variable [CommSemiring R] [Fintype n] [Fintype m] [DecidableEq m] [DecidableEq n]
  [Semiring A] [Algebra R A]

theorem reindexAlgEquiv_apply (e : m ≃ n) (M : Matrix m m A) :
    Matrix.reindexAlgEquiv R A e M = reindex e e M := rfl

