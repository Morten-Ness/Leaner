import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem diag_conjTranspose [Star α] (A : Matrix n n α) :
    diag Aᴴ = star (diag A) := rfl

