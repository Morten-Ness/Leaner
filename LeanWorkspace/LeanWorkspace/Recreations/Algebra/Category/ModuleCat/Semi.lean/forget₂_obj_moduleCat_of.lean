import Mathlib

variable (R : Type u) [Semiring R]

theorem forget₂_obj_moduleCat_of (X : Type v) [AddCommMonoid X] [Module R X] :
    (forget₂ (SemimoduleCat R) AddCommMonCat).obj (of R X) = .of X := rfl

