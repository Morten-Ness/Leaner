import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem one_smul (x : X') : (1 : B) • x = x := match x with
  | fromCoset y => by
    change fromCoset _ = fromCoset _
    simp only [one_leftCoset]
  | ∞ => rfl

