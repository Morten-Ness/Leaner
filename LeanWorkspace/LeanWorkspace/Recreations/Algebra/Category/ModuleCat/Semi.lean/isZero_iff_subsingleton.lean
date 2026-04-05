import Mathlib

variable (R : Type u) [Semiring R]

variable {X₁ X₂ : Type v}

variable {M N : SemimoduleCat.{v} R}

theorem isZero_iff_subsingleton : IsZero M ↔ Subsingleton M where
  mp := SemimoduleCat.subsingleton_of_isZero
  mpr _ := SemimoduleCat.isZero_of_subsingleton M

