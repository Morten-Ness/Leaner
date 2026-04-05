import Mathlib

variable {l m n o : Type*} {l' m' n' o' : Type*} {m'' n'' : Type*}

variable (R A : Type*)

variable [CommSemiring R] [Fintype n] [Fintype m] [DecidableEq m] [DecidableEq n]
  [Semiring A] [Algebra R A]

theorem reindexAlgEquiv_symm (e : m ≃ n) : (Matrix.reindexAlgEquiv R A e).symm =
    Matrix.reindexAlgEquiv R A e.symm := rfl

