import Mathlib

variable {A M G α β γ : Type*}

variable (e : Perm α) {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)

theorem extendDomain_one : extendDomain 1 f = 1 := extendDomain_refl f

