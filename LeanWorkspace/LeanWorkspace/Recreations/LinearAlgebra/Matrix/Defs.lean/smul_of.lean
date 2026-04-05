import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem smul_of [SMul R α] (r : R) (f : m → n → α) : r • Matrix.of f = Matrix.of (r • f) := rfl

