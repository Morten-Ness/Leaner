import Mathlib

variable (R : Type u) [CommSemiring R]

variable (X : Type v)

variable (X : Type u)

theorem cardinalMk_eq_max [Nonempty X] [Nontrivial R] : #(FreeAlgebra R X) = #R ⊔ #X ⊔ ℵ₀ := by
  simp

