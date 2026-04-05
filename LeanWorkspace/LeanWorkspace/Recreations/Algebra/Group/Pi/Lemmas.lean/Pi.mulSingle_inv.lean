import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable [DecidableEq I]

theorem Pi.mulSingle_inv [∀ i, Group <| f i] (i : I) (x : f i) :
    mulSingle i x⁻¹ = (mulSingle i x)⁻¹ := (MonoidHom.mulSingle f i).map_inv x

