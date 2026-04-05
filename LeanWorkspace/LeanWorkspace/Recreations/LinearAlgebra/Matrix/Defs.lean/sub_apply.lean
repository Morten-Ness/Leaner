import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem sub_apply [Sub α] (A B : Matrix m n α) (i : m) (j : n) :
    (A - B) i j = (A i j) - (B i j) := rfl

