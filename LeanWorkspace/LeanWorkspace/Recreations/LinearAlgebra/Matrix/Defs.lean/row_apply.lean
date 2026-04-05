import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem row_apply (A : Matrix m n α) (i : m) (j : n) : A.row i j = A i j := rfl

