import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable [DecidableEq I]

theorem Pi.mulSingle_sup [∀ i, SemilatticeSup (f i)] [∀ i, One (f i)] (i : I) (x y : f i) :
    Pi.mulSingle i (x ⊔ y) = Pi.mulSingle i x ⊔ Pi.mulSingle i y := Function.update_sup _ _ _ _

