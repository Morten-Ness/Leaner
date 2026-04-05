import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

variable [DecidableEq n]

theorem diagonal_conjTranspose [AddMonoid α] [StarAddMonoid α] (v : n → α) :
    (diagonal v)ᴴ = diagonal (star v) := by
  rw [Matrix.conjTranspose, diagonal_transpose, diagonal_map (star_zero _)]
  rfl

