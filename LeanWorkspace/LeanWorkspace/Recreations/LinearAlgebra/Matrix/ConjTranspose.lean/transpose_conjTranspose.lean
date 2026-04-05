import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem transpose_conjTranspose [Star α] (M : Matrix m n α) :
    Mᵀᴴ = M.map star := rfl

