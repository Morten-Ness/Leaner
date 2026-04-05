import Mathlib

variable {l m n o : Type*} {l' m' n' o' : Type*} {m'' n'' : Type*}

variable (R A : Type*)

variable [CommSemiring R] [Fintype n] [Fintype m] [DecidableEq m] [DecidableEq n]
  [Semiring A] [Algebra R A]

theorem reindexAlgEquiv_refl : Matrix.reindexAlgEquiv R A (Equiv.refl m) = AlgEquiv.refl := AlgEquiv.ext fun _ => rfl

