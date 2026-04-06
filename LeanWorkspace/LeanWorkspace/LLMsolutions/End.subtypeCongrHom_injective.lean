FAIL
import Mathlib

variable {A M G α β γ : Type*}

theorem subtypeCongrHom_injective (p : α → Prop) [DecidablePred p] :
    Function.Injective (Equiv.Perm.subtypeCongrHom p) := by
  intro e₁ e₂ h
  ext x
  exact congrArg Subtype.val (congrArg (fun f => f x) h)
