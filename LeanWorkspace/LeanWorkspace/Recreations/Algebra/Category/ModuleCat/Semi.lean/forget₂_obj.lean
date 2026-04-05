import Mathlib

variable (R : Type u) [Semiring R]

theorem forget₂_obj (X : SemimoduleCat R) :
    (forget₂ (SemimoduleCat R) AddCommMonCat).obj X = .of X := rfl

