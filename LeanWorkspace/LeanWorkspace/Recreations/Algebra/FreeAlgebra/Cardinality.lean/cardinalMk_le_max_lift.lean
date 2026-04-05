import Mathlib

variable (R : Type u) [CommSemiring R]

variable (X : Type v)

theorem cardinalMk_le_max_lift :
    #(FreeAlgebra R X) ≤ Cardinal.lift.{v} #R ⊔ Cardinal.lift.{u} #X ⊔ ℵ₀ := by
  cases subsingleton_or_nontrivial R
  · exact (FreeAlgebra.cardinalMk_eq_one R X).trans_le (le_max_of_le_right one_le_aleph0)
  cases isEmpty_or_nonempty X
  · exact (FreeAlgebra.cardinalMk_eq_lift R X).trans_le (le_max_of_le_left <| le_max_left _ _)
  · exact (FreeAlgebra.cardinalMk_eq_max_lift R X).le

