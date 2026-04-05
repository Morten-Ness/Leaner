import Mathlib

variable {α : Type u} [Mul α]

theorem quot_mk_assoc_left (x y z w : α) :
    Quot.mk (AssocRel α) (x * (y * z * w)) = Quot.mk _ (x * (y * (z * w))) := Quot.sound (AssocRel.left _ _ _ _)

