import Mathlib

variable {R S : Type*} (n : Type*) [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]

variable (f : R →+* S)

theorem univ_coeff_eval₂Hom (M : n × n → S) (i : ℕ) :
    MvPolynomial.eval₂Hom f M ((univ R n).coeff i) =
      (Matrix.charpoly (Matrix.of M.curry)).coeff i := by
  rw [← Matrix.charpoly.univ_map_eval₂Hom n f M, Polynomial.coeff_map]

