import Mathlib

variable {A M G α β γ : Type*}

variable (e : Perm α) {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)

theorem extendDomain_mul (e e' : Equiv.Perm α) :
    e.extendDomain f * e'.extendDomain f = (e * e').extendDomain f := extendDomain_trans _ _ _

