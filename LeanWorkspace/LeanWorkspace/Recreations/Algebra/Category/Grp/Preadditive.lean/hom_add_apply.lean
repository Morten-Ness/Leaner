import Mathlib

variable {M N : AddCommGrpCat.{u}}

theorem hom_add_apply {P Q : AddCommGrpCat} (f g : P ⟶ Q) (x : P) : (f + g) x = f x + g x := rfl

