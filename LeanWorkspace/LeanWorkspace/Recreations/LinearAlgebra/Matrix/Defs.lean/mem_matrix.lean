import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem mem_matrix {S : Set α} {M : Matrix m n α} :
    M ∈ S.matrix ↔ ∀ i j, M i j ∈ S := .rfl

