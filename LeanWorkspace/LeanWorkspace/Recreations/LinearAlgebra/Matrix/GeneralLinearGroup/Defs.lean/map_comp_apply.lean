import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v}

variable [CommRing R]

variable {S T : Type*} [CommRing S] [CommRing T]

theorem map_comp_apply (f : T →+* R) (g : R →+* S) (x : GL n T) :
    (Matrix.GeneralLinearGroup.map g).comp (Matrix.GeneralLinearGroup.map f) x = Matrix.GeneralLinearGroup.map g (Matrix.GeneralLinearGroup.map f x) := rfl

