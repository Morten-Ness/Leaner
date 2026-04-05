import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

variable {S : Set α}

theorem submatrix_mem_matrix_iff {M : Matrix m n α} {r : l → m} {c : o → n}
    (hr : Function.Surjective r) (hc : Function.Surjective c) :
    M.submatrix r c ∈ S.matrix ↔ M ∈ S.matrix := ⟨(hr.forall.mpr fun _ => hc.forall.mpr fun _ => · _ _), Matrix.submatrix_mem_matrix⟩

