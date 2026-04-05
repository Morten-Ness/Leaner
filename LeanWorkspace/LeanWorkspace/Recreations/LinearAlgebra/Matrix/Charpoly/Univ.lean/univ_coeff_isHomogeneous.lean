import Mathlib

variable {R S : Type*} (n : Type*) [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]

variable (f : R →+* S)

theorem univ_coeff_isHomogeneous (i j : ℕ) (h : i + j = Fintype.card n) :
    ((univ R n).coeff i).IsHomogeneous j := (Matrix.charpoly.optionEquivLeft_symm_univ_isHomogeneous R n).coeff_isHomogeneous_of_optionEquivLeft_symm _ _ h

