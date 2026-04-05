import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable [∀ i, Mul <| f i]

theorem Commute.pi {x y : ∀ i, f i} (h : ∀ i, Commute (x i) (y i)) : Commute x y := SemiconjBy.pi h

