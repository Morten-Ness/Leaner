import Mathlib

variable {R S : Type*} (n : Type*) [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]

variable (f : R →+* S)

theorem univ_monic : (univ R n).Monic := charpoly_monic (mvPolynomialX n n R)

