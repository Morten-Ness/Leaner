import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable [DecidableEq I]

theorem Pi.mulSingle_zpow [∀ i, Group (f i)] (i : I) (x : f i) (n : ℤ) :
    mulSingle i (x ^ n) = mulSingle i x ^ n := (MonoidHom.mulSingle f i).map_zpow x n

