import Mathlib

variable (R : Type u) [CommSemiring R]

variable (X : Type v)

variable (X : Type u)

theorem cardinalMk_le_max : #(FreeAlgebra R X) ≤ #R ⊔ #X ⊔ ℵ₀ := by
  simpa using FreeAlgebra.cardinalMk_le_max_lift R X

