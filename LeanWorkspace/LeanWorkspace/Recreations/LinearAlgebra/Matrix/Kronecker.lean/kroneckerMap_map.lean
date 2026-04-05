import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

theorem kroneckerMap_map (f : α → β → γ) (g : γ → γ') (A : Matrix l m α) (B : Matrix n p β) :
    (Matrix.kroneckerMap f A B).map g = Matrix.kroneckerMap (fun a b => g (f a b)) A B := ext fun _ _ => rfl

