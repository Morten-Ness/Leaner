import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [CommSemiring R] [CommSemiring S]

theorem eval_C_X_eval₂_map_C_X {p : R[X][Y]} :
    eval (C X) (eval₂ (mapRingHom <| algebraMap R R[X][Y]) (C Y) p) = p := congr($Polynomial.eval_C_X_comp_eval₂_map_C_X p)

