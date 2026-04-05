import Mathlib

variable {A M G α β γ : Type*}

variable (e : Perm α) {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)

theorem extendDomainHom_injective : Function.Injective (Equiv.Perm.extendDomainHom f) := (injective_iff_map_eq_one (Equiv.Perm.extendDomainHom f)).mpr fun e he =>
    ext fun x => f.injective <|
      Subtype.ext ((extendDomain_apply_image e f x).symm.trans (Equiv.Perm.ext_iff.mp he (f x)))

