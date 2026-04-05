import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p : R[X]}

theorem monic_of_isUnit_leadingCoeff_inv_smul (h : IsUnit p.leadingCoeff) :
    Polynomial.Monic (h.unit⁻¹ • p) := by
  rw [Polynomial.Monic.def, Polynomial.leadingCoeff_smul_of_smul_regular _ (isSMulRegular_of_group _), Units.smul_def]
  simp

