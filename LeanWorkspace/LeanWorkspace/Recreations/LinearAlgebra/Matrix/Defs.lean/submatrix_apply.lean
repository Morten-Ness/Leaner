import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem submatrix_apply (A : Matrix m n α) (r : l → m) (c : o → n) (i j) :
    A.submatrix r c i j = A (r i) (c j) := rfl

