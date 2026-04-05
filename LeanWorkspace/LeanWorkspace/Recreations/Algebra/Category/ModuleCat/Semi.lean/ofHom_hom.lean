import Mathlib

variable (R : Type u) [Semiring R]

theorem ofHom_hom {M N : SemimoduleCat.{v} R} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

