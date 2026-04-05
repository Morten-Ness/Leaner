import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [Semiring R] [Semiring S] (f : R →+* S) (p : R[X][Y]) (q : R[X])

theorem map_mapRingHom_eval_map : (p.map <| mapRingHom f).eval (q.map f) = (p.eval q).map f := by
  rw [eval_map, ← coe_mapRingHom, eval₂_hom]

