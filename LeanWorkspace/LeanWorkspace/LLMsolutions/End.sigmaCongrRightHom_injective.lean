import Mathlib

variable {A M G α β γ : Type*}

theorem sigmaCongrRightHom_injective {α : Type*} {β : α → Type*} :
    Function.Injective (Equiv.Perm.sigmaCongrRightHom β) := by
  intro e₁ e₂ h
  ext x y
  have h' := congrArg (fun e => e ⟨x, y⟩) h
  simpa using h'
