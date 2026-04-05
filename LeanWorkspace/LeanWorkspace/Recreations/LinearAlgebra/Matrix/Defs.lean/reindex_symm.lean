import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem reindex_symm (eₘ : m ≃ l) (eₙ : n ≃ o) :
    (Matrix.reindex eₘ eₙ).symm = (Matrix.reindex eₘ.symm eₙ.symm : Matrix l o α ≃ _) := rfl

