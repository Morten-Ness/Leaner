import Mathlib

theorem ofHom_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

