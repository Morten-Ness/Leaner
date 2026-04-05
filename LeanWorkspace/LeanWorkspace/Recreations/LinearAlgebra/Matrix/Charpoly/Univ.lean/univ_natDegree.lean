import Mathlib

variable {R S : Type*} (n : Type*) [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]

variable (f : R →+* S)

theorem univ_natDegree [Nontrivial R] : (univ R n).natDegree = Fintype.card n := charpoly_natDegree_eq_dim (mvPolynomialX n n R)

