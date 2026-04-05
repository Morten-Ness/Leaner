import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

theorem single_kronecker_single
    [MulZeroClass α] [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ia : l) (ja : m) (ib : n) (jb : p) (a b : α) :
    single ia ja a ⊗ₖ single ib jb b = single (ia, ib) (ja, jb) (a * b) := Matrix.kroneckerMap_single_single _ _ _ _ _ zero_mul mul_zero _ _

