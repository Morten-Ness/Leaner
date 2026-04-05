import Mathlib

variable (R : Type u) [Ring R]

variable {X₁ X₂ : Type v}

variable {M N : ModuleCat.{v} R}

theorem isZero_iff_subsingleton : IsZero M ↔ Subsingleton M where
  mp := ModuleCat.subsingleton_of_isZero
  mpr _ := ModuleCat.isZero_of_subsingleton M

