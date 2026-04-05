import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem submatrix_id_id (A : Matrix m n α) : A.submatrix id id = A := Matrix.ext fun _ _ => rfl

