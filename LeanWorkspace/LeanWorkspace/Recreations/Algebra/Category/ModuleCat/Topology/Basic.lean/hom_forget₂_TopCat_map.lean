import Mathlib

variable (R : Type u) [Ring R] [TopologicalSpace R]

theorem hom_forget₂_TopCat_map {X Y : TopModuleCat R} (f : X ⟶ Y) :
    ((forget₂ _ TopCat).map f).hom = f.hom := rfl

