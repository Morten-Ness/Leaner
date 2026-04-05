import Mathlib

theorem hom_ofHom {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : (ofHom f).hom = f := rfl

