import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem ext_col {A B : Matrix m n α} (h : ∀ j, A.col j = B.col j) : A = B := Matrix.ext fun i j => congr_fun (h j) i

