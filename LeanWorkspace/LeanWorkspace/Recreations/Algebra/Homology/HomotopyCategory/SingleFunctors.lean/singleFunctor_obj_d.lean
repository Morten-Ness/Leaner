import Mathlib

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]

set_option backward.isDefEq.respectTransparency false in
theorem singleFunctor_obj_d (X : C) (n p q : ℤ) :
    ((singleFunctor C n).obj X).d p q = 0 := rfl

