import Mathlib

variable (R : Type u) [Ring R]

theorem forget₂_map (X Y : ModuleCat R) (f : X ⟶ Y) :
    (forget₂ (ModuleCat R) AddCommGrpCat).map f = AddCommGrpCat.ofHom f.hom := rfl

