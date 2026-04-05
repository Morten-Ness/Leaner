import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem reindex_refl_refl (A : Matrix m n α) : Matrix.reindex (Equiv.refl _) (Equiv.refl _) A = A := A.submatrix_id_id

