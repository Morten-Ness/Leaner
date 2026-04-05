import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem ext_row {A B : Matrix m n α} (h : ∀ i, A.row i = B.row i) : A = B := Matrix.ext fun i j => congr_fun (h i) j

