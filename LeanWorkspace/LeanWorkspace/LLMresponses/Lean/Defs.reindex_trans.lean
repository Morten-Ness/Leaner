import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem reindex_trans {l₂ o₂ : Type*} (eₘ : m ≃ l) (eₙ : n ≃ o) (eₘ₂ : l ≃ l₂) (eₙ₂ : o ≃ o₂) :
    (Matrix.reindex eₘ eₙ).trans (Matrix.reindex eₘ₂ eₙ₂) =
      (Matrix.reindex (eₘ.trans eₘ₂) (eₙ.trans eₙ₂) : Matrix m n α ≃ _) := by
  ext M i j <;> rfl
