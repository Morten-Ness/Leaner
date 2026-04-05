import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem of_col (f : m → n → α) : (Matrix.of f)ᵀ.col = f := rfl

