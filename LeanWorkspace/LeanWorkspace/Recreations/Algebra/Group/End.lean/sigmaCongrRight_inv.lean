import Mathlib

variable {A M G α β γ : Type*}

theorem sigmaCongrRight_inv {α : Type*} {β : α → Type*} (F : ∀ a, Equiv.Perm (β a)) :
    (sigmaCongrRight F)⁻¹ = sigmaCongrRight fun a => (F a)⁻¹ := rfl

