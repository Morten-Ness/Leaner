import Mathlib

variable (R : Type u) [Semiring R]

theorem forget₂_map (X Y : SemimoduleCat R) (f : X ⟶ Y) :
    (forget₂ (SemimoduleCat R) AddCommMonCat).map f = AddCommMonCat.ofHom f.hom := rfl

