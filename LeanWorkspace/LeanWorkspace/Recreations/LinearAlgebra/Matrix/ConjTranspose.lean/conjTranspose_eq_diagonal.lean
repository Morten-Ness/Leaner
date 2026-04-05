import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem conjTranspose_eq_diagonal [DecidableEq n] [AddMonoid α] [StarAddMonoid α]
    {M : Matrix n n α} {v : n → α} :
    Mᴴ = diagonal v ↔ M = diagonal (star v) := (Function.Involutive.eq_iff Matrix.conjTranspose_conjTranspose).trans <|
    by rw [Matrix.diagonal_conjTranspose]

