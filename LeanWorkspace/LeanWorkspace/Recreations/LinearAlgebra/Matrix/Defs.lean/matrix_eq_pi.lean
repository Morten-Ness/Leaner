import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem matrix_eq_pi {S : Set α} :
    S.matrix = Matrix.of.symm ⁻¹' Set.univ.pi fun (_ : m) ↦ Set.univ.pi fun (_ : n) ↦ S := by
  ext
  simp [Set.mem_matrix]

