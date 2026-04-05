import Mathlib

variable {A : Type*}

theorem _root_.Units.isStrictlyPositive_of_le [LE A] [Monoid A] [Zero A] {a : Aˣ}
    (h : (0 : A) ≤ a) : IsStrictlyPositive (a : A) := a.isStrictlyPositive_iff.mpr h

