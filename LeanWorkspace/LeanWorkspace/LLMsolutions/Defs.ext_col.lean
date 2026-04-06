import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem ext_col {A B : Matrix m n α} (h : ∀ j, A.col j = B.col j) : A = B := by
  ext i j
  simpa [Matrix.col] using congrArg (fun c => c i) (h j)
