import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem col_map (A : Matrix m n α) (f : α → β) (j : n) : (A.map f).col j = f ∘ A.col j := rfl

