import Mathlib

section

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem ext_col {A B : Matrix m n α} (h : ∀ j, A.col j = B.col j) : A = B := Matrix.ext fun i j => congr_fun (h j) i

end

section

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

variable {M N : Matrix m n α}

theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N := ⟨fun h => funext fun i => funext <| h i, fun h => by simp [h]⟩

end

section

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem ext_row {A B : Matrix m n α} (h : ∀ i, A.row i = B.row i) : A = B := Matrix.ext fun i j => congr_fun (h i) j

end

section

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective fun M : Matrix m n α => M.map f := fun _ _ h =>
  Matrix.ext fun i j => hf <| Matrix.ext_iff.mpr h i j

end

section

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem neg_apply [Neg α] (A : Matrix m n α) (i : m) (j : n) :
    (-A) i j = -(A i j) := rfl

set_option backward.isDefEq.respectTransparency false in

end

section

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem reindex_trans {l₂ o₂ : Type*} (eₘ : m ≃ l) (eₙ : n ≃ o) (eₘ₂ : l ≃ l₂) (eₙ₂ : o ≃ o₂) :
    (Matrix.reindex eₘ eₙ).trans (Matrix.reindex eₘ₂ eₙ₂) =
      (Matrix.reindex (eₘ.trans eₘ₂) (eₙ.trans eₙ₂) : Matrix m n α ≃ _) := Equiv.ext fun A => (A.submatrix_submatrix eₘ.symm eₙ.symm eₘ₂.symm eₙ₂.symm :)

end

section

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

variable {S : Set α}

theorem submatrix_mem_matrix_iff {M : Matrix m n α} {r : l → m} {c : o → n}
    (hr : Function.Surjective r) (hc : Function.Surjective c) :
    M.submatrix r c ∈ S.matrix ↔ M ∈ S.matrix := ⟨(hr.forall.mpr fun _ => hc.forall.mpr fun _ => · _ _), Matrix.submatrix_mem_matrix⟩

end

section

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem transpose_injective : Function.Injective (Matrix.transpose : Matrix m n α → Matrix n m α) := fun _ _ h => Matrix.ext fun i j => Matrix.ext_iff.2 h j i

end
