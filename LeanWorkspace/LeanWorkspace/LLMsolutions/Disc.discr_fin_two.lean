FAIL
import Mathlib

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

theorem discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) :
    A.discr = A.trace ^ 2 - 4 * A.det := by
  simp [Matrix.discr, Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_two, pow_two]
  ring_nf
