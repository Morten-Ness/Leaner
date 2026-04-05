import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem conjTranspose_eq_one [DecidableEq n] [NonAssocSemiring α] [StarRing α] {M : Matrix n n α} :
    Mᴴ = 1 ↔ M = 1 := (Function.Involutive.eq_iff Matrix.conjTranspose_conjTranspose).trans <|
    by rw [Matrix.conjTranspose_one]

