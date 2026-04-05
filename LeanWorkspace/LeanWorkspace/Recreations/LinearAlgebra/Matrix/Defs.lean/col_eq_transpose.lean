import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem col_eq_transpose (A : Matrix m n α) : A.col = Matrix.of.symm Aᵀ := rfl

