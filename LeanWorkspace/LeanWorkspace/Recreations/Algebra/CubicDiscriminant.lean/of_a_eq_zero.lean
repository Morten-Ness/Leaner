import Mathlib

variable {R S F K : Type*}

variable {P Q : Cubic R} {a b c d a' b' c' d' : R} [Semiring R]

private theorem coeffs : (∀ n > 3, P.toPoly.coeff n = 0) ∧ P.toPoly.coeff 3 = P.a ∧
    P.toPoly.coeff 2 = P.b ∧ P.toPoly.coeff 1 = P.c ∧ P.toPoly.coeff 0 = P.d := by
  simp only [Cubic.toPoly, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow]
  grind [zero_add]


theorem of_a_eq_zero (ha : P.a = 0) : P.toPoly = Polynomial.C P.b * Polynomial.X ^ 2 + Polynomial.C P.c * Polynomial.X + Polynomial.C P.d := by
  rw [Cubic.toPoly, ha, C_0, zero_mul, zero_add]

