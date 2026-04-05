import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem updateRow_idem [DecidableEq m] (A : Matrix m n α) (i : m) (x y : n → α) :
    (A.updateRow i x).updateRow i y = A.updateRow i y := Function.update_idem _ _ _

