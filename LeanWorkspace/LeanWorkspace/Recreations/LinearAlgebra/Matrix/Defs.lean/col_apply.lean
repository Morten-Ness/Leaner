import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem col_apply (A : Matrix m n α) (i : n) (j : m) : A.col i j = A j i := rfl

