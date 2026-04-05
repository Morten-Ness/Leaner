import Mathlib

variable (R : Type u) [Ring R] [TopologicalSpace R]

theorem forget₂_TopCat_obj {X : TopModuleCat R} : ((forget₂ _ TopCat).obj X : Type _) = X := rfl

