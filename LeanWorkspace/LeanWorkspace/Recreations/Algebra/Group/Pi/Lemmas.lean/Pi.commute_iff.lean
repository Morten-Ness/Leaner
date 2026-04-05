import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable [∀ i, Mul <| f i]

theorem Pi.commute_iff {x y : ∀ i, f i} : Commute x y ↔ ∀ i, Commute (x i) (y i) := semiconjBy_iff

