import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem col_submatrix_eq_comp {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ → m) (c : n₀ → n) (j : n₀) :
    (A.submatrix r c).col j = A.col (c j) ∘ r := rfl

