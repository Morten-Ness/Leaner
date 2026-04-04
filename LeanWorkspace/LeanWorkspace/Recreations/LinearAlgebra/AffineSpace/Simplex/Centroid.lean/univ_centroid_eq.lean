import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem univ_centroid_eq (s : Affine.Simplex k P n) :
    Finset.univ.centroid k s.points = s.centroid := rfl

