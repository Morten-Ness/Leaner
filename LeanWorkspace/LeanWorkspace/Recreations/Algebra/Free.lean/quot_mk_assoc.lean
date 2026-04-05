import Mathlib

variable {α : Type u} [Mul α]

theorem quot_mk_assoc (x y z : α) : Quot.mk (AssocRel α) (x * y * z) = Quot.mk _ (x * (y * z)) := Quot.sound (AssocRel.intro _ _ _)

