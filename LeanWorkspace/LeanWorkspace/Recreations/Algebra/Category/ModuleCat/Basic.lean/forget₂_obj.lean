import Mathlib

variable (R : Type u) [Ring R]

theorem forget₂_obj (X : ModuleCat R) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj X = AddCommGrpCat.of X := rfl

