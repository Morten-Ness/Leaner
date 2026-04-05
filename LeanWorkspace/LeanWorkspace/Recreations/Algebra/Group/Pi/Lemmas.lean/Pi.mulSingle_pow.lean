import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable [DecidableEq I]

theorem Pi.mulSingle_pow [∀ i, Monoid (f i)] (i : I) (x : f i) (n : ℕ) :
    mulSingle i (x ^ n) = mulSingle i x ^ n := (MonoidHom.mulSingle f i).map_pow x n

