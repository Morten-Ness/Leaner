import Mathlib

variable (R : Type u) [CommRing R]

theorem Iso.conj_hom_eq_conj {V W : FGModuleCat R} (i : V ≅ W) (f : End V) :
    (Iso.conj i f).hom.hom = (LinearEquiv.conj (FGModuleCat.isoToLinearEquiv i) f.hom.hom) := rfl

