import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

variable {S : Set α}

theorem submatrix_mem_matrix {M : Matrix m n α} {r : l → m} {c : o → n} (hM : M ∈ S.matrix) :
    M.submatrix r c ∈ S.matrix := by simp_all [Set.mem_matrix]

