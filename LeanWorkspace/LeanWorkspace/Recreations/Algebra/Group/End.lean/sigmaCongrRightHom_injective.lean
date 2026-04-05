import Mathlib

variable {A M G α β γ : Type*}

theorem sigmaCongrRightHom_injective {α : Type*} {β : α → Type*} :
    Function.Injective (Equiv.Perm.sigmaCongrRightHom β) := by
  intro x y h
  ext a b
  simpa using Equiv.congr_fun h ⟨a, b⟩

