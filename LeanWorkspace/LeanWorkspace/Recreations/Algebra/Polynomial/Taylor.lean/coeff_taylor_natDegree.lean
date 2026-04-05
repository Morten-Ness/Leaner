import Mathlib

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

theorem coeff_taylor_natDegree : (Polynomial.taylor r f).coeff f.natDegree = f.leadingCoeff := by
  by_cases hf : f = 0
  · rw [hf, map_zero, coeff_natDegree]
  · rw [Polynomial.taylor_coeff, hasseDeriv_natDegree_eq_C, eval_C]

