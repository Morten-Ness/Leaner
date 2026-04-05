import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable [DecidableEq I] [∀ i, Preorder (f i)] [∀ i, One (f i)]

theorem mulSingle_strictMono : StrictMono (Pi.mulSingle i : f i → ∀ i, f i) := Function.update_strictMono

