import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem row_submatrix {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ → m) (c : n₀ → n) (i : m₀) :
    (A.submatrix r c).row i = (A.submatrix id c).row (r i) := rfl

