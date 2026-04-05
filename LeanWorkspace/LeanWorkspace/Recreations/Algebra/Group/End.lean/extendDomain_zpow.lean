import Mathlib

variable {A M G α β γ : Type*}

variable (e : Perm α) {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)

theorem extendDomain_zpow (n : ℤ) : (e ^ n).extendDomain f = e.extendDomain f ^ n := map_zpow (Equiv.Perm.extendDomainHom f) _ _

