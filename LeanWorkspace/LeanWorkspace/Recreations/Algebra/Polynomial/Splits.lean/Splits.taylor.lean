import Mathlib

variable {R : Type*}

variable [CommSemiring R]

theorem Splits.taylor {p : R[X]} (hp : p.Splits) (r : R) : (p.taylor r).Splits := by
  have (i : _) : (X + C r + C i).Splits := by simpa [add_assoc] using Polynomial.Splits.X_add_C (r + i)
  induction hp using Submonoid.closure_induction <;> aesop

