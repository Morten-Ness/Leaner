import Mathlib

variable {R S : Type*} (n : Type*) [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]

variable (f : R →+* S)

theorem univ_coeff_card : (univ R n).coeff (Fintype.card n) = 1 := by
  suffices Polynomial.coeff (univ ℤ n) (Fintype.card n) = 1 by
    rw [← Matrix.charpoly.univ_map_map n (Int.castRingHom R), Polynomial.coeff_map, this, map_one]
  rw [← Matrix.charpoly.univ_natDegree ℤ n]
  exact (Matrix.charpoly.univ_monic ℤ n).leadingCoeff

