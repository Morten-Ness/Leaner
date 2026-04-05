import Mathlib

variable {R : Type*} [CommSemiring R] (r : R) (f : R[X])

theorem taylor_taylor (f : R[X]) (r s : R) : Polynomial.taylor r (Polynomial.taylor s f) = Polynomial.taylor (r + s) f := by
  simp only [Polynomial.taylor_apply, comp_assoc, map_add, add_comp, X_comp, C_comp, add_assoc]

