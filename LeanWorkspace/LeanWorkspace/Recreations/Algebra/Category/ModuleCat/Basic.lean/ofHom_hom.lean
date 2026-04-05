import Mathlib

variable (R : Type u) [Ring R]

theorem ofHom_hom {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

