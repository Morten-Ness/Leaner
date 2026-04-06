import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

variable {S : Set α}

theorem submatrix_mem_matrix_iff {M : Matrix m n α} {r : l → m} {c : o → n}
    (hr : Function.Surjective r) (hc : Function.Surjective c) :
    M.submatrix r c ∈ S.matrix ↔ M ∈ S.matrix := by
  constructor
  · intro h i j
    rcases hr i with ⟨i', rfl⟩
    rcases hc j with ⟨j', rfl⟩
    exact h i' j'
  · intro h i j
    exact h (r i) (c j)
