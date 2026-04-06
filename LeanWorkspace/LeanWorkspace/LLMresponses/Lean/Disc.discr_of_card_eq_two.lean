FAIL
import Mathlib

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

theorem discr_of_card_eq_two (A : Matrix n n R) (hn : Fintype.card n = 2) :
    A.discr = A.trace ^ 2 - 4 * A.det := by
  classical
  let e : n ≃ Fin 2 := Fintype.equivFinOfCardEq hn
  let B : Matrix (Fin 2) (Fin 2) R := Matrix.reindex e e A
  have htrB : B.trace = B 0 0 + B 1 1 := by
    simp [Matrix.trace, B]
  have hB : B.discr = B.trace ^ 2 - 4 * B.det := by
    rw [htrB, Matrix.discr, Matrix.det_fin_two]
    ring
  have htrace : A.trace = B.trace := by
    rw [htrB]
    simp [Matrix.trace, B, e]
  have hdet : A.det = B.det := by
    symm
    simpa [B, e] using Matrix.det_reindex_self A e
  have hdiscr : A.discr = B.discr := by
    rw [Matrix.discr, Matrix.discr]
    congr 1
    simpa [Matrix.charpoly, B, e] using Matrix.det_reindex_self (Matrix.X - Matrix.map A) e
  rw [hdiscr, htrace, hdet]
  exact hB
