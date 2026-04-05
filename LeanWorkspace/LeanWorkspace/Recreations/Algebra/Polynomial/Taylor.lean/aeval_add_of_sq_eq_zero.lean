import Mathlib

variable {R : Type*} [CommSemiring R] (r : R) (f : R[X])

theorem aeval_add_of_sq_eq_zero {S : Type*} [CommRing S] [Algebra R S]
    (p : R[X]) (x y : S) (hy : y ^ 2 = 0) :
    p.aeval (x + y) = p.aeval x + p.derivative.aeval x * y := by
  simp only [← eval_map_algebraMap, Polynomial.eval_add_of_sq_eq_zero _ _ _ hy, derivative_map]

