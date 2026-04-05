import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

theorem kroneckerMap_map_left (f : α' → β → γ) (g : α → α') (A : Matrix l m α) (B : Matrix n p β) :
    Matrix.kroneckerMap f (A.map g) B = Matrix.kroneckerMap (fun a b => f (g a) b) A B := ext fun _ _ => rfl

