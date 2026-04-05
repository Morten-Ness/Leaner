import Mathlib

section

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

theorem discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) :
    A.discr = A.trace ^ 2 - 4 * A.det := A.discr_of_card_eq_two <| Fintype.card_fin _

end

section

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

theorem discr_of_card_eq_two (A : Matrix n n R) (hn : Fintype.card n = 2) :
    A.discr = A.trace ^ 2 - 4 * A.det := by
  nontriviality R
  rw [Matrix.discr, Polynomial.discr_of_degree_eq_two (by simp; norm_cast)]
  simp [A.charpoly_of_card_eq_two hn]

end
