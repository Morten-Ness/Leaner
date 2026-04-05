import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem conjTranspose_intCast [DecidableEq n] [Ring α] [StarRing α] (d : ℤ) :
    (d : Matrix n n α)ᴴ = d := by
  simp [Matrix.conjTranspose, Matrix.map_intCast, diagonal_intCast]

