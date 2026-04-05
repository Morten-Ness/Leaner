import Mathlib

open scoped Nat

variable {R S : Type*}

variable [CommSemiring R] {A : Type*} [CommRing A] [Algebra R A]

theorem aeval_sumIDeriv_eq_eval (p : R[X]) (r : A) :
    aeval r (Polynomial.sumIDeriv p) = eval r (Polynomial.sumIDeriv (map (algebraMap R A) p)) := by
  rw [aeval_def, eval, Polynomial.sumIDeriv_map, eval₂_map, RingHom.id_comp]

