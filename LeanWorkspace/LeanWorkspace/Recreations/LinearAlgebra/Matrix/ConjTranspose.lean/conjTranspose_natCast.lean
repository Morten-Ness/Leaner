import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem conjTranspose_natCast [DecidableEq n] [NonAssocSemiring α] [StarRing α] (d : ℕ) :
    (d : Matrix n n α)ᴴ = d := by
  simp [Matrix.conjTranspose, Matrix.map_natCast, diagonal_natCast]

