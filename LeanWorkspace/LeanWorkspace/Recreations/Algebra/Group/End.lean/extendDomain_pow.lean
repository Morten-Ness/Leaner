import Mathlib

variable {A M G α β γ : Type*}

variable (e : Perm α) {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)

theorem extendDomain_pow (n : ℕ) : (e ^ n).extendDomain f = e.extendDomain f ^ n := map_pow (Equiv.Perm.extendDomainHom f) _ _

