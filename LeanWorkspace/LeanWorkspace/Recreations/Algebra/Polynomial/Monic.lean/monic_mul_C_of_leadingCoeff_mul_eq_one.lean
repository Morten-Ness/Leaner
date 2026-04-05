import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem monic_mul_C_of_leadingCoeff_mul_eq_one {b : R} (hp : p.leadingCoeff * b = 1) :
    Polynomial.Monic (p * Polynomial.C b) := by
  unfold Polynomial.Monic
  nontriviality
  rw [leadingCoeff_mul' _] <;> simp [leadingCoeff_C b, hp]

