import Mathlib

open scoped Polynomial.Bivariate

variable {R S : Type*}

variable [CommSemiring R] [CommSemiring S]

theorem eval_C_X_comp_eval₂_map_C_X :
    (evalRingHom (C X : R[X][Y])).comp (eval₂RingHom (mapRingHom <| algebraMap R R[X][Y]) (C Y)) =
      .id _ := by
  ext <;> simp

