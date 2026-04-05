import Mathlib

variable {A : Type*}

theorem _root_.isStrictlyPositive_one [LE A] [Monoid A] [Zero A] [ZeroLEOneClass A] :
    IsStrictlyPositive (1 : A) := IsStrictlyPositive.iff_of_unital.mpr ⟨zero_le_one, isUnit_one⟩

