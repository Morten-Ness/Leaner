import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem toUnits_injective : Function.Injective (Unitary.toUnits : unitary R → Rˣ) := fun _ _ h =>
  Subtype.ext <| Units.ext_iff.mp h

