import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem star_eq_conjTranspose [Star α] (M : Matrix m m α) : star M = Mᴴ := rfl

