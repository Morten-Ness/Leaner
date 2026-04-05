import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem mul_smul (b b' : B) (x : X') : (b * b') • x = b • b' • x := match x with
  | fromCoset y => by
    change fromCoset _ = fromCoset _
    simp only [leftCoset_assoc]
  | ∞ => rfl

