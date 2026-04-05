import Mathlib

variable {R : Type*}

variable [Semiring R]

variable [Nontrivial R]

theorem isMonicOfDegree_X : IsMonicOfDegree (X : R[X]) 1 := (Polynomial.isMonicOfDegree_iff ..).mpr ⟨natDegree_X_le, coeff_X_one⟩

