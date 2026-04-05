import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem of_add_of [Add α] (f g : m → n → α) : Matrix.of f + Matrix.of g = Matrix.of (f + g) := rfl

