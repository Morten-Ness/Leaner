import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem conjTranspose_transpose [Star α] (M : Matrix m n α) :
    Mᴴᵀ = M.map star := rfl

