import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v}

variable [CommRing R]

variable {S T : Type*} [CommRing S] [CommRing T]

theorem map_id : Matrix.GeneralLinearGroup.map (RingHom.id R) = MonoidHom.id (GL n R) := rfl

