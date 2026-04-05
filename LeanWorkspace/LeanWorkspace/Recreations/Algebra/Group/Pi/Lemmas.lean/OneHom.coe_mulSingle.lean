import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable [DecidableEq I]

theorem OneHom.coe_mulSingle [∀ i, One <| f i] (i : I) :
    mulSingle f i = Pi.mulSingle (M := f) i := rfl

