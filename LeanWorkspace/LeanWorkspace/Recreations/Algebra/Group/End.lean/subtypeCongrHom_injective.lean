import Mathlib

variable {A M G α β γ : Type*}

theorem subtypeCongrHom_injective (p : α → Prop) [DecidablePred p] :
    Function.Injective (Equiv.Perm.subtypeCongrHom p) := by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk_inj]
  constructor <;> ext i <;> simpa using Equiv.congr_fun h i

