import Mathlib

variable {α M : Type*} [One M]

theorem HasFiniteMulSupport.sup [SemilatticeSup M] {f g : α → M} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) :
    HasFiniteMulSupport fun a ↦ f a ⊔ g a := (hf.union hg).subset <| mulSupport_sup ..

