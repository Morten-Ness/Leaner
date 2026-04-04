import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem centroid_eq_affineCombination (s : Affine.Simplex k P n) :
    s.centroid = Finset.affineCombination k Finset.univ s.points (Finset.centroidWeights k Finset.univ) := by rfl

