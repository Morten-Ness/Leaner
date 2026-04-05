import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem row_map (A : Matrix m n α) (f : α → β) (i : m) : (A.map f).row i = f ∘ A.row i := rfl

