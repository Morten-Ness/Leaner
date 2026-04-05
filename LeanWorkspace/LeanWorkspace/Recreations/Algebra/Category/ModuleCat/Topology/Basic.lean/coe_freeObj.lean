import Mathlib

variable (R : Type u) [Ring R] [TopologicalSpace R]

theorem coe_freeObj (X : TopCat.{v}) : TopModuleCat.freeObj R X = (X →₀ R) := rfl

