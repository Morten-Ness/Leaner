import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem of_apply (f : m → n → α) (i j) : Matrix.of f i j = f i j := rfl

