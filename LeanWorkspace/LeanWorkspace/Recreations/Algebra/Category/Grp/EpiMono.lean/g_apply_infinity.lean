import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem g_apply_infinity (x : B) : (GrpCat.SurjectiveOfEpiAuxs.g x) ∞ = ∞ := rfl

