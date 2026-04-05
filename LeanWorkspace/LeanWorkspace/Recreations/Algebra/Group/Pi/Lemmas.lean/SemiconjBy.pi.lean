import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable [∀ i, Mul <| f i]

theorem SemiconjBy.pi {x y z : ∀ i, f i} (h : ∀ i, SemiconjBy (x i) (y i) (z i)) :
    SemiconjBy x y z := funext h

