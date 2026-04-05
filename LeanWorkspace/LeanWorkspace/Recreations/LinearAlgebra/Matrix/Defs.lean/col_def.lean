import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem col_def (A : Matrix m n α) : A.col = fun j ↦ Aᵀ j := rfl

