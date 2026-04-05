import Mathlib

variable {A M G α β γ : Type*}

variable (e : Perm α) {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)

theorem extendDomain_eq_one_iff {e : Equiv.Perm α} {f : α ≃ Subtype p} : e.extendDomain f = 1 ↔ e = 1 := (injective_iff_map_eq_one' (Equiv.Perm.extendDomainHom f)).mp (Equiv.Perm.extendDomainHom_injective f) e

