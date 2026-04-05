import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem neg_of [Neg α] (f : m → n → α) : -Matrix.of f = Matrix.of (-f) := rfl

