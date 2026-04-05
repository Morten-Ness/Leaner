import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

theorem kroneckerMap_add_right [Add β] [Add γ] (f : α → β → γ)
    (hf : ∀ a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) (A : Matrix l m α) (B₁ B₂ : Matrix n p β) :
    Matrix.kroneckerMap f A (B₁ + B₂) = Matrix.kroneckerMap f A B₁ + Matrix.kroneckerMap f A B₂ := ext fun _ _ => hf _ _ _

