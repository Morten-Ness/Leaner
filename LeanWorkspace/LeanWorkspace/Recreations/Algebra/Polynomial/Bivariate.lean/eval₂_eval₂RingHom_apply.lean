import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [CommSemiring R] [CommSemiring S]

theorem eval₂_eval₂RingHom_apply (f : R →+* S) (x y : S) (p : R[X][Y]) :
    eval₂ (eval₂RingHom f x) y p = (p.map <| mapRingHom f).evalEval x y := congr($(Polynomial.eval₂RingHom_eval₂RingHom f x y) p)

