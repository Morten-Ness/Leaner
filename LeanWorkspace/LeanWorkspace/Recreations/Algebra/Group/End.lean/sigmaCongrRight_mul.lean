import Mathlib

variable {A M G α β γ : Type*}

theorem sigmaCongrRight_mul {α : Type*} {β : α → Type*} (F : ∀ a, Equiv.Perm (β a))
    (G : ∀ a, Equiv.Perm (β a)) : sigmaCongrRight F * sigmaCongrRight G = sigmaCongrRight (F * G) := rfl

