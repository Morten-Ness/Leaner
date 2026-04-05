import Mathlib

variable {A : Type*}

theorem _root_.IsUnit.isStrictlyPositive [LE A] [Monoid A] [Zero A]
    {a : A} (ha : IsUnit a) (ha₀ : 0 ≤ a) : IsStrictlyPositive a := IsStrictlyPositive.iff_of_unital.mpr ⟨ha₀, ha⟩

