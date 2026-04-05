import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem zero_apply [Zero α] (i : m) (j : n) : (0 : Matrix m n α) i j = 0 := rfl

