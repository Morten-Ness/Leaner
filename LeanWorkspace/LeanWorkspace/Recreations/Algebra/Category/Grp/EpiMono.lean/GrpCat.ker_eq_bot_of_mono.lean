import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem ker_eq_bot_of_mono [Mono f] : f.hom.ker = ⊥ := MonoidHom.ker_eq_bot_of_cancel fun u v h => ConcreteCategory.ext_iff.mp <|
    (@cancel_mono _ _ _ _ _ f _ (ofHom u) (ofHom v)).1 <| ConcreteCategory.ext h

