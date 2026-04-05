import Mathlib

variable {R S : Type*} (n : Type*) [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]

variable (f : R →+* S)

theorem univ_map_map :
    (univ R n).map (MvPolynomial.map f) = univ S n := by
  rw [MvPolynomial.map, Matrix.charpoly.univ_map_eval₂Hom]; rfl

