import Mathlib

variable {A M G α β γ : Type*}

theorem sigmaCongrRight_one {α : Type*} {β : α → Type*} :
    sigmaCongrRight (1 : ∀ a, Equiv.Perm <| β a) = 1 := rfl

