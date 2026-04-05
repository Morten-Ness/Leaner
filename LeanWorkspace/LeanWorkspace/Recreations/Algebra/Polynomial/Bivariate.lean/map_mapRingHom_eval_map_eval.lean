import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [Semiring R] [Semiring S] (f : R →+* S) (p : R[X][Y]) (q : R[X])

theorem map_mapRingHom_eval_map_eval (r : R) :
    ((p.map <| mapRingHom f).eval <| q.map f).eval (f r) = f ((p.eval q).eval r) := by
  rw [Polynomial.map_mapRingHom_eval_map, eval_map, eval₂_hom]

