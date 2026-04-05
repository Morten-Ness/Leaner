import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable [DecidableEq I]

theorem OneHom.mulSingle_apply [∀ i, One <| f i] (i : I) (x : f i) :
    mulSingle f i x = Pi.mulSingle i x := rfl

