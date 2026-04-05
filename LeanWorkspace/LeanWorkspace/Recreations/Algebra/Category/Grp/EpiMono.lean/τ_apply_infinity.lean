import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem τ_apply_infinity : τ ∞ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := Equiv.swap_apply_right _ _

