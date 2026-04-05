import Mathlib

variable {A M G α β γ : Type*}

variable (e : Perm α) {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)

theorem extendDomain_inv : (e.extendDomain f)⁻¹ = e⁻¹.extendDomain f := rfl

