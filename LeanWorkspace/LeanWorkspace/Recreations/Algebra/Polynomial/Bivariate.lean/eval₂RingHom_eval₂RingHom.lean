import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [CommSemiring R] [CommSemiring S]

theorem eval₂RingHom_eval₂RingHom (f : R →+* S) (x y : S) :
    eval₂RingHom (eval₂RingHom f x) y =
      (evalEvalRingHom x y).comp (mapRingHom <| mapRingHom f) := by
  ext <;> simp

