import Mathlib

variable {l m n o : Type*} {l' m' n' o' : Type*} {m'' n'' : Type*}

variable (R A : Type*)

theorem det_reindexAlgEquiv (B : Type*) [CommSemiring R] [CommRing B] [Algebra R B] [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) (A : Matrix m m B) :
    det (Matrix.reindexAlgEquiv R B e A) = det A := det_reindex_self e A

