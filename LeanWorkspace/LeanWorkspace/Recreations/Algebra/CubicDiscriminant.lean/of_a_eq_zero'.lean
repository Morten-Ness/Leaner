import Mathlib

variable {R S F K : Type*}

variable {P Q : Cubic R} {a b c d a' b' c' d' : R} [Semiring R]

private theorem coeffs : (∀ n > 3, P.toPoly.coeff n = 0) ∧ P.toPoly.coeff 3 = P.a ∧
    P.toPoly.coeff 2 = P.b ∧ P.toPoly.coeff 1 = P.c ∧ P.toPoly.coeff 0 = P.d := by
  simp only [Cubic.toPoly, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow]
  grind [zero_add]


theorem of_a_eq_zero' : Cubic.toPoly ⟨0, b, c, d⟩ = Polynomial.C b * Polynomial.X ^ 2 + Polynomial.C c * Polynomial.X + Polynomial.C d := Cubic.of_a_eq_zero rfl

