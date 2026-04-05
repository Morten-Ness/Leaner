import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

variable {S : Set α}

theorem transpose_mem_matrix_iff {M : Matrix m n α} :
    Mᵀ ∈ S.matrix ↔ M ∈ S.matrix := forall_comm

