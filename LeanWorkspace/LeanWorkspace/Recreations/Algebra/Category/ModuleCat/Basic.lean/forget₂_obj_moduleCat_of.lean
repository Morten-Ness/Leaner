import Mathlib

variable (R : Type u) [Ring R]

theorem forget₂_obj_moduleCat_of (X : Type v) [AddCommGroup X] [Module R X] :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj (of R X) = AddCommGrpCat.of X := rfl

