import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

theorem kroneckerMap_transpose (f : α → β → γ) (A : Matrix l m α) (B : Matrix n p β) :
    Matrix.kroneckerMap f Aᵀ Bᵀ = (Matrix.kroneckerMap f A B)ᵀ := ext fun _ _ => rfl

