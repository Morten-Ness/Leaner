import Mathlib

variable {A : Type*}

theorem iff_of_unital [LE A] [Monoid A] [Zero A] {a : A} :
    IsStrictlyPositive a ↔ 0 ≤ a ∧ IsUnit a := Iff.rfl

