import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem monic_C_mul_of_mul_leadingCoeff_eq_one {b : R} (hp : b * p.leadingCoeff = 1) :
    Polynomial.Monic (Polynomial.C b * p) := by
  unfold Polynomial.Monic
  nontriviality
  rw [leadingCoeff_mul' _] <;> simp [leadingCoeff_C b, hp]

