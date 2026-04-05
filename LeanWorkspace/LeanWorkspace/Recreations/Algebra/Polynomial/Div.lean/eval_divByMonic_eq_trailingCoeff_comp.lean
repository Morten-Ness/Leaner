import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem eval_divByMonic_eq_trailingCoeff_comp {p : R[X]} {t : R} :
    (p /ₘ (Polynomial.X - Polynomial.C t) ^ p.rootMultiplicity t).eval t = (p.comp (Polynomial.X + Polynomial.C t)).trailingCoeff := by
  obtain rfl | hp := eq_or_ne p 0
  · rw [Polynomial.zero_divByMonic, eval_zero, zero_comp, trailingCoeff_zero]
  have mul_eq := Polynomial.pow_mul_divByMonic_rootMultiplicity_eq p t
  set m := p.rootMultiplicity t
  set g := p /ₘ (Polynomial.X - Polynomial.C t) ^ m
  have : (g.comp (Polynomial.X + Polynomial.C t)).coeff 0 = g.eval t := by
    rw [coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C, zero_add]
  rw [← congr_arg (comp · <| Polynomial.X + Polynomial.C t) mul_eq, mul_comp, pow_comp, sub_comp, X_comp, C_comp,
    add_sub_cancel_right, ← reverse_leadingCoeff, reverse_X_pow_mul, reverse_leadingCoeff,
    trailingCoeff, Nat.le_zero.1 (natTrailingDegree_le_of_ne_zero <|
      this ▸ Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero t hp), this]

