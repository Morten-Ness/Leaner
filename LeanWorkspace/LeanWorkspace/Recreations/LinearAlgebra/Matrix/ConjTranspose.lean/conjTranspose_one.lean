import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem conjTranspose_one [DecidableEq n] [NonAssocSemiring α] [StarRing α] :
    (1 : Matrix n n α)ᴴ = 1 := by
  simp [Matrix.conjTranspose]

