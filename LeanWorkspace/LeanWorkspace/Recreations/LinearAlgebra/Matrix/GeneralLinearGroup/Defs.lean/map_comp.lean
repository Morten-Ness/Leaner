import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v}

variable [CommRing R]

variable {S T : Type*} [CommRing S] [CommRing T]

theorem map_comp (f : T →+* R) (g : R →+* S) :
    Matrix.GeneralLinearGroup.map (g.comp f) = (Matrix.GeneralLinearGroup.map g).comp (Matrix.GeneralLinearGroup.map (n := n) f) :=
  rfl

