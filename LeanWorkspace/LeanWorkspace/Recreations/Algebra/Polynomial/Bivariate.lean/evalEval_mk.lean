import Mathlib

open scoped Polynomial.Bivariate Polynomial

variable {R : Type*} [CommRing R] {x y : R} {p : R[X][Y]} (h : p.evalEval x y = 0)

theorem evalEval_mk (g : R[X][Y]) : evalEval h (AdjoinRoot.mk p g) = g.evalEval x y := by
  rw [evalEval, lift_mk, Polynomial.eval₂_evalRingHom]

