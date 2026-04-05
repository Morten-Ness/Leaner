import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem transpose_injective : Function.Injective (Matrix.transpose : Matrix m n α → Matrix n m α) := fun _ _ h => Matrix.ext fun i j => Matrix.ext_iff.2 h j i

