import Mathlib

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

theorem discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) :
    A.discr = A.trace ^ 2 - 4 * A.det := A.discr_of_card_eq_two <| Fintype.card_fin _

