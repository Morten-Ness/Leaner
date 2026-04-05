import Mathlib

theorem ofHom_apply {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) : ofHom f r = f r := rfl

