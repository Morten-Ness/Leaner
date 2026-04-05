import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem transpose_transpose (M : Matrix m n α) : Mᵀᵀ = M := by
  ext
  rfl

