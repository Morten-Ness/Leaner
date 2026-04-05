import Mathlib

variable {R : Type*}

variable [Semiring R]

variable [Nontrivial R]

theorem isMonicOfDegree_X_pow (n : ℕ) : IsMonicOfDegree ((X : R[X]) ^ n) n := (Polynomial.isMonicOfDegree_iff ..).mpr ⟨natDegree_X_pow_le n, coeff_X_pow_self n⟩

