import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem transpose_injective : Function.Injective (Matrix.transpose : Matrix m n α → Matrix n m α) := by
  intro A B h
  ext i j
  have := congrArg (fun M : Matrix n m α => M j i) h
  simpa [Matrix.transpose] using this
