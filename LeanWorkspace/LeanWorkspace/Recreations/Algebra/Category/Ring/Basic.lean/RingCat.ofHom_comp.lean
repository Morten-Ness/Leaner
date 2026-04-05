import Mathlib

theorem ofHom_comp {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (f : R →+* S) (g : S →+* T) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

